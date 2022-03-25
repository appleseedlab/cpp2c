(*  Transformations.v
    Definition of the transformation that Cpp2C performs as well as some
    lemmas concerning it
*)

Require Import
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  EvalRules
  SideEffects
  MapLemmas
  NoCallsFromFunctionTable
  NoMacroInvocations
  NoVarsInEnvironment.


Inductive TransformExpr :
  macro_table -> function_table -> expr -> function_table -> expr -> Prop :=


  | Transform_Num : forall M F z,
    (* Identity transformation *)
    TransformExpr M F (Num z) F (Num z)


  | Transform_Var : forall M F x,
    (* Identity transformation *)
    TransformExpr M F (Var x) F (Var x)


  | Transform_ParenExpr : forall M F e0 F' e0',
    (* Transform the inner expression *)
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (ParenExpr e0) F' (ParenExpr e0')


  | Transform_UnExpr : forall M F e0 F' e0' uo,
    (* Transform the inner expression *)
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (UnExpr uo e0) F' (UnExpr uo e0')


  | Transform_BinExpr : forall bo M F e1 e2 F' F'' F1result F2result e1' e2',

    (* Transform the left operand *)
    TransformExpr M F e1 F' e1' ->
    F' = StringMapProperties.update F F1result ->

    (* Transform the right operand *)
    TransformExpr M F' e2 F'' e2' ->
    F'' = StringMapProperties.update F' F2result ->

    (* e1' does not contain calls to functions that were added
       while transforming e2 *)
    ExprNoCallsFromFunctionTable e1' F2result ->

    (* e2 does not contain calls to functions that were added
       while transforming e1 *)
    ExprNoCallsFromFunctionTable e2 F1result ->

    TransformExpr M F (BinExpr bo e1 e2) F'' (BinExpr bo e1' e2')


  | Transform_Assign : forall M F x e F' e',
    (* Transform the inner expression *)
    TransformExpr M F e F' e' ->
    TransformExpr M F (Assign x e) F' (Assign x e')


  | Transform_FunctionCall :
    forall   F M x es F' es' Fesresult params fstmt fexpr,

    (*  The callee is not a macro and is in the function table *)
    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->

    (*  Transform function arguments *)
    TransformExprList M F es F' es' ->
    F' = StringMapProperties.update F Fesresult ->

    (*  fstmt does not contain calls to functions that were added
        while transforming es *)
    StmtNoCallsFromFunctionTable fstmt Fesresult ->

    (*  fexpr does not contain calls to functions that were added
        while transforming es *)
    ExprNoCallsFromFunctionTable fexpr Fesresult ->

    (*  None of the functions that were added while transforming es have
        the same name as the callee *)
    ~ StringMap.In (elt:=function_definition) x Fesresult ->

    (*  Note that we don't transform the function definition here. That is
        because we transform a function when we encounter its definition,
        not a call to it. This lets us transform recursive functions
        more easily. *)
    TransformExpr M F (CallOrInvocation x es) F' (CallOrInvocation x es')


  | Transform_MacroIdentity :
    forall F M x es params mexpr,

    (* TODO: Decide if we should recursively transform macros if one part
       of them makes the unable to be transformed.
       For now we don't transform them at all. *)

    StringMap.MapsTo x (params, mexpr) M ->

    (* We don't transform the macro if:
       - One of its arguments has side-effects
       - Its body has side-effects
       - Its body shares variables with its caller's environment
    *)
    ~ Forall ExprNoSideEffects es \/
    ~ ExprNoSideEffects mexpr \/
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x nil) v S' ->
      ~ ExprNoVarsInLocalEnvironment mexpr E) ->

    TransformExpr M F (CallOrInvocation x es) F (CallOrInvocation x es)

  (*  Note: This could potentially recurse infinitely if the argument contains
      a macro invocation. Since we stipulate that the argument is side-effect
      free, however, and treat all macro invocations as having side-effects,
      this cannot happen. *)
  (*  TODO: Transform macro arguments? *)
  | Transform_Macro :
    forall  M F F' x params mexpr mexpr' es newdef
            fname Fresult Fesresult F'' es' S'0 es'0,

    StringMap.MapsTo x (params, mexpr) M ->

    (*  The macro arguments contain no side-effects *)
    ExprListNoSideEffects es ->

    (*  mexpr has no side-effects *)
    ExprNoSideEffects mexpr ->

    (*  Assert that we could evaluate this macro's arguments *)
    (forall S E G v1 S',
      EvalExpr S E G F M (CallOrInvocation x es) v1 S' ->
      EvalExprList S E G F M es S'0 es'0) ->

    (*  Assert that if we were to evaluate the argument store for this macro,
        expressions evaluated under the resulting store would evaluate the same
        under the original store.
        Also assert that if we can evaluate the macro under the original *)
    ( forall S E G S' es es',
      EvalExprList S E G F M es S' es' ->
        forall ls Sargs Sargs',
        (*  Call-by-name store vs. call-by-value store *)
        NatMap.Equal Sargs (NatMapProperties.of_list (combine ls es)) ->
        NatMap.Equal Sargs'(NatMapProperties.of_list (combine ls es')) ->

        forall SMacro SFunction,
        (*  Macro argument mapping and function argument mapping *)
        NatMap.Equal SMacro (NatMapProperties.update S Sargs) ->
        NatMap.Equal SFunction (NatMapProperties.update S Sargs') ->

        forall Em E',
        (*  Function and macro environment mappings *)
        StringMap.Equal Em (StringMapProperties.of_list (combine params ls)) ->
        StringMap.Equal E' (StringMapProperties.update E Em) ->

        (*  Conclusion: Evaluation is the same under the pre-evaluated store and non-pre
            evaluated store, and the expression can be evaluated under macro environment
            mapping without being joined with the caller's environment *)
        (
          (
            forall v S', (EvalExpr SMacro E' G F M mexpr v S' <-> EvalExpr SFunction E' G F M mexpr v S') /\
            EvalExpr SFunction Em G F M mexpr v S'
          )
        )
      ) ->

    (*  Transform the macro arguments *)
    TransformExprList M F es F' es' ->
    F' = StringMapProperties.update F Fesresult ->

    (*  Transform the macro body *)
    TransformExpr M F' mexpr F'' mexpr' ->
    (* Create the transformed definition *)
    newdef = (params, Skip, mexpr') ->
    Fresult = (StringMap.add fname newdef (StringMap.empty function_definition)) ->
    F'' = StringMapProperties.update F' Fresult ->

    (*  The original macro body does not reference any functions
        added while transforming the arguments *)
    ExprNoCallsFromFunctionTable mexpr Fesresult ->

    (*  The original and transformed arguments do not reference
        the transformed function *)
    ExprListNoCallsFromFunctionTable es Fresult ->
    ExprListNoCallsFromFunctionTable es' Fresult ->

    (*  The transformed arguments do not have side-effects
        (we could prove this if were to define side-effect
        freedom inductively, but that's beyond the scope of this proof *)
    ExprListNoSideEffects es' ->

    (*  The transformed macro body does not have side-effects
        (again, we could prove this but it should be obvious *)
    ExprNoSideEffects mexpr' ->

    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F' ->

    TransformExpr M F (CallOrInvocation x es) F'' (CallOrInvocation fname es')
with TransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=

  | Transform_Skip : forall M F,
    TransformStmt M F Skip F Skip

  | Transform_Expr : forall M F e F' e',
    (*  Transform the inner expression *)
    TransformExpr M F e F' e' ->
    TransformStmt M F (Expr e) F' (Expr e')

  | Transform_If : forall M F cond s1 s2 F' F'' F''' cond' s1' s2' Fcondresult Fs1result Fs2result,
    (*  Transform the condition *)
    TransformExpr M F cond F' cond' ->
    F' = StringMapProperties.update F Fcondresult ->

    (*  Transform the true branch *)
    TransformStmt M F' s1 F'' s1' ->
    F'' = StringMapProperties.update F' Fs1result ->

    (*  Transform the false branch *)
    TransformStmt M F'' s2 F''' s2' ->
    F''' = StringMapProperties.update F'' Fs2result ->

    (*  The transformed condition does not call any functions
        that were added while transforming the true and false branches *)
    ExprNoCallsFromFunctionTable cond' Fs1result ->
    ExprNoCallsFromFunctionTable cond' Fs2result ->

    (*  The original true branch does not call any functions that were added
        while transforming the condition, and the transformed true branch
        does not call any functions that were added while transforming the
        false branch *)
    StmtNoCallsFromFunctionTable s1 Fcondresult ->
    StmtNoCallsFromFunctionTable s1' Fs2result ->

    (*  The original false branch does not call any functions that were added
        while transforming the condition or true branch *)
    StmtNoCallsFromFunctionTable s2 Fcondresult ->
    StmtNoCallsFromFunctionTable s2 Fs1result ->

    TransformStmt M F (IfElse cond s1 s2) F''' (IfElse cond' s1' s2')

  | Transform_While : forall M F cond s0 F' F'' cond' s0' Fcondresult Fs0result,
    (*  Transform the condition *)
    TransformExpr M F cond F' cond' ->
    F' = StringMapProperties.update F Fcondresult ->

    (*  Transform the body *)
    TransformStmt M F' s0 F'' s0' ->
    F'' = StringMapProperties.update F' Fs0result ->

    (*  The original condition does not call any function that were
        added while transforming the condition or while body, and
        the transformed condition does not call any functions that were
        added while transforming the while body *)
    ExprNoCallsFromFunctionTable cond Fcondresult ->
    ExprNoCallsFromFunctionTable cond Fs0result ->
    ExprNoCallsFromFunctionTable cond' Fs0result ->

    (*  The original while body does not call any functions that were added
        while transforming the condition or the while body *)
    StmtNoCallsFromFunctionTable s0 Fcondresult ->
    StmtNoCallsFromFunctionTable s0 Fs0result ->

    (*  The original statement, as a whole, does not refer to functions
        that were added while transforming it *)
    StmtNoCallsFromFunctionTable (While cond s0) Fcondresult ->
    StmtNoCallsFromFunctionTable (While cond s0) Fs0result ->

    (*  If we were to transform the original while loop again
        under the transformed function table, then we would get
        the same transformed condition and statement and not add
        any new functions to the function table *)
    TransformStmt M F'' (While cond s0) F'' (While cond' s0') ->

    TransformStmt M F (While cond s0) F'' (While cond' s0')

  | Transform_Compound_nil : forall M F,
    TransformStmt M F (Compound nil) F (Compound nil)

  | Transform_Compound_cons : forall M F s ss F' F'' s' ss' Fsresult Fssresult,
    (*  Transform first statement *)
    TransformStmt M F s F' s' ->
    F' = StringMapProperties.update F Fsresult ->

    (*  Transform the remaining statements *)
    TransformStmt M F' (Compound ss) F'' (Compound ss') ->
    F'' = StringMapProperties.update F' Fssresult ->

    (*  The transformed first statement does not call any functions
        that were added while transforming the remaining statements *)
    StmtNoCallsFromFunctionTable s' Fssresult ->

    (*  The original remaining statement don't call any functions that
        were added while transforming the first statement *)
    StmtNoCallsFromFunctionTable (Compound ss) Fsresult ->

    TransformStmt M F (Compound (s::ss)) F'' (Compound (s'::ss'))
with TransformExprList :
  macro_table -> function_table -> list expr ->
  function_table -> list expr -> Prop :=

  (* End of arguments *)
  | TransformExprList_Nil : forall M F,
    TransformExprList M F nil F nil

  (* There are arguments left to transform *)
  | TransformExprList_Cons : forall M F e es F' F'' e' es' Feresult Fesresult,
    (* Transform the first expression *)
    TransformExpr M F e F' e' ->
    F' = StringMapProperties.update F Feresult ->

    (* Transform the remaining expressions *)
    TransformExprList M F' es F'' es' ->
    F'' = StringMapProperties.update F' Fesresult ->

    (*  The transformed expression does not call any functions that
        were added while transforming the rest of the the expressions *)
    ExprNoCallsFromFunctionTable e' Fesresult ->

    (*  None of the untransformed expressions called a function that was added
        while transforming the first expression *)
    ExprListNoCallsFromFunctionTable es Feresult ->

    TransformExprList M F (e::es) F'' (e'::es').

(*  Custom induction scheme *)
Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformStmt_mut := Induction for TransformStmt Sort Prop
with TransformExprList_mut := Induction for TransformExprList Sort Prop.

Lemma TransformExprList_length : forall es M F F' es',
  TransformExprList M F es F' es' ->
  List.length es = List.length es'.
Proof.
  induction es.
  - intros. inversion_clear H. auto.
  - intros. inversion_clear H.
    apply IHes in H2.
    simpl. auto.
Qed.

