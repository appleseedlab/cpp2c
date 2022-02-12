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
  macro_table -> function_table -> expr ->
  function_table -> expr -> Prop :=

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

    (* What I find interesting here is what we *don't* need to add
       as premises in order for the proof to work *)

    (* e1 does not contain calls are to functions that were added
       while transforming e2 *)
    (* ExprNoCallsFromFunctionTable e1 F M F2result -> *)

    (* e1' does not contain calls to functions that were added
       while transforming e2 *)
    ExprNoCallsFromFunctionTable e1' F' M F2result ->

    (* e2 does not contain calls to functions that were added
       while transforming e1 *)
    ExprNoCallsFromFunctionTable e2 F M F1result ->

    (* e2' does not contain calls to functions that were added
       while transforming e1 *)
    (* ExprNoCallsFromFunctionTable e2' F'' M F1result -> *)

    TransformExpr M F (BinExpr bo e1 e2) F'' (BinExpr bo e1' e2')

  | Transform_Assign : forall M F x e F' e',
    TransformExpr M F e F' e' ->
    TransformExpr M F (Assign x e) F' (Assign x e')

  | Transform_FunctionCall :
    forall   F M x es F' F'' F''' F'''' es' newdef
             params fstmt fexpr fstmt' fexpr'
             Fesresult Fstmtresult Fexprresult,

    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    (*  We have not already transformed this function *)
    ~StringMap.MapsTo x (params, fstmt', fexpr') F ->

    (* Transform function arguments *)
    TransformExprList M F es F' es' ->
    F' = StringMapProperties.update F Fesresult ->

    (* Transform function statement *)
    TransformStmt M F' fstmt F'' fstmt' ->
    F'' = StringMapProperties.update F' Fstmtresult ->

    (* Transform function return expression *)
    TransformExpr M F'' fexpr F''' fexpr' ->
    F''' =  StringMapProperties.update F'' Fexprresult ->

    (* Create the new definition of the function *)
    newdef = (params, fstmt', fexpr') ->

    (* es' does not contain calls to functions that
       were added while transforming fstmt or fexpr or
       the transformed function *)
    ExprListNoCallsFromFunctionTable es' F' M Fstmtresult ->
    ExprListNoCallsFromFunctionTable es' F'' M Fexprresult ->
    ExprListFunctionNotCalled es' F''' M x newdef ->

    (* fstmt' does not contain calls to functions that
       were added while transforming fexpr or the transformed function *)
    StmtNoCallsFromFunctionTable fstmt' F'' M Fexprresult ->
    StmtFunctionNotCalled fstmt' F''' M x newdef ->

    (* fexpr' does not contain a call to the transformed function or
       to functions that were added while transforming fstmt *)
    ExprFunctionNotCalled fexpr' F''' M x newdef ->

    (* fexpr does not contain calls to functions that were added
       while transforming fstmt or es *)
    ExprNoCallsFromFunctionTable fexpr F M Fstmtresult ->
    ExprNoCallsFromFunctionTable fexpr F' M Fstmtresult ->
    ExprNoCallsFromFunctionTable fexpr F M Fesresult ->

    (* fstmt does not contain calls to functions that were added
       while transforming es *)
    StmtNoCallsFromFunctionTable fstmt F M Fesresult ->

    (* Add the transformed function back to the function table under a new name *)
    F'''' = StringMapProperties.update F'''
      (StringMap.add x newdef (StringMap.empty function_definition)) ->

    TransformExpr M F (CallOrInvocation x es) F'''' (CallOrInvocation x es')

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
    Exists ExprHasSideEffects es \/
    ExprHasSideEffects mexpr \/
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x nil) v S' ->
      ~ ExprNoVarsInEnvironment mexpr E) ->

    TransformExpr M F (CallOrInvocation x es) F (CallOrInvocation x es)

  | Transform_FunctionLikeMacroBodyIsVarNoSharedVars1ArgNoSideEffects :
    forall F M x y p e e' F' fname newdef,

    StringMap.MapsTo x ((p::nil), (Var y)) M ->

    (*  e is a side-effect-free expression *)
    ~ ExprHasSideEffects e ->

    (* The macro's variable is not from its caller's environment *)
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x (e::nil)) v S' ->
      ExprNoVarsInEnvironment (Var y) E) ->

    (* Transform macro argument *)
    TransformExpr M F e F' e' ->

    (* Create the transformed definition *)
    newdef = ((p::nil), Skip, (Var y)) ->

    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F ->
    F' = StringMapProperties.update F (StringMap.add fname newdef (StringMap.empty function_definition)) ->

    TransformExpr M F (CallOrInvocation x (e::nil)) F' (CallOrInvocation fname (e::nil))


  | Transform_ObjectLikeMacroNoSideEffectsNoSharedVarsNoNestedMacros :
    forall F M x F' mexpr mexpr' fname newdef,

    StringMap.MapsTo x (nil, mexpr) M ->

    (* The macro does not have side-effects *)
    ~ ExprHasSideEffects mexpr ->
    (* The macro does not contain nested macro invocations *)
    ExprNoMacroInvocations mexpr F M ->

    (* The macro does not share variables with its caller's environment *)
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x nil) v S' ->
      ExprNoVarsInEnvironment mexpr E) ->

    (* Transform macro body *)
    TransformExpr M F mexpr F' mexpr' ->

    (* Create the transformed definition *)
    newdef = (nil, Skip, mexpr') ->

    (* mexpr' does not contain a call to the transformed function *)
    ExprFunctionNotCalled mexpr' F' M x newdef ->

    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F ->
    F' = StringMap.add fname newdef F ->

    TransformExpr M F (CallOrInvocation x nil) F' (CallOrInvocation fname nil)
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

    (*  TODO: Add comments *)
    ExprNoCallsFromFunctionTable e' F' M Fesresult ->

    (*  None of the untransformed expressions called a function that was added
        while transforming the first expression *)
    ExprListNoCallsFromFunctionTable es F M Feresult ->

    TransformExprList M F (e::es) F'' (e'::es')
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

    (*  TODO: Add comments *)
    ExprNoCallsFromFunctionTable cond' F' M Fs1result ->
    ExprNoCallsFromFunctionTable cond' F'' M Fs2result ->

    (*  TODO: Add comments *)
    StmtNoCallsFromFunctionTable s1 F M Fcondresult ->
    StmtNoCallsFromFunctionTable s1' F'' M Fs2result ->

    (*  TODO: Add comments *)
    StmtNoCallsFromFunctionTable s2 F M Fcondresult ->
    StmtNoCallsFromFunctionTable s2 F' M Fs1result ->

    TransformStmt M F (IfElse cond s1 s2) F''' (IfElse cond' s1' s2')

  | Transform_While : forall M F cond s0 F' F'' cond' s0' Fcondresult Fs0result,
    (*  Transform the condition *)
    TransformExpr M F cond F' cond' ->
    F' = StringMapProperties.update F Fcondresult ->

    (*  Transform the body *)
    TransformStmt M F' s0 F'' s0' ->
    F'' = StringMapProperties.update F' Fs0result ->

    (*  TODO: Add comments *)
    ExprNoCallsFromFunctionTable cond F M Fcondresult ->
    ExprNoCallsFromFunctionTable cond F' M Fs0result ->
    ExprNoCallsFromFunctionTable cond' F' M Fs0result ->

    (*  TODO: Add comments *)
    StmtNoCallsFromFunctionTable s0 F M Fcondresult ->
    StmtNoCallsFromFunctionTable s0 F' M Fs0result ->

    (*  This premise looks weird, but is needed for the transformation
        soundness proof to work.
        Since while loops are inductively defined by themselves,
        the transformation for them must be as well.
        We consider the transformation a success if its untransformed
        and transformed expression evaluate to the same value and store,
        and its transformed statement evaluate to the same store. *)
    (
      forall S E G v S' S'',

      (*  Untransformed *)
      EvalExpr S E G F M cond v S' ->
      EvalStmt S' E G F M s0 S'' ->

      (*  Transformed *)
      EvalExpr S E G F' M cond' v S' ->
      EvalStmt S' E G F'' M s0' S'' ->
      TransformStmt M F (While cond s0) F'' (While cond' s0')
    ) ->

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

    (*  TODO: Add comments *)
    StmtNoCallsFromFunctionTable s' F' M Fssresult ->

    (*  TODO: Add comments *)
    StmtNoCallsFromFunctionTable (Compound ss) F M Fsresult ->

    TransformStmt M F (Compound (s::ss)) F'' (Compound (s'::ss')).


(*  Custom induction scheme *)
Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformExprList_mut := Induction for TransformExprList Sort Prop
with TransformStmt_mut := Induction for TransformStmt Sort Prop.


(*  If an expression does not contain any macro invocations, then
    after transformation it remains unchanged *)
Lemma TransformExpr_ExprNoMacroInvocations_e_eq : forall M F e F' e' ,
  TransformExpr M F e F' e' ->
  ExprNoMacroInvocations e F M ->
  e = e'.
Proof.
  apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
      ExprNoMacroInvocations e F M ->
      e = e')
    (* TransformExprList *)
    (fun M F es F' es' (h : TransformExprList M F es F' es') =>
      ExprListNoMacroInvocations es F M ->
      es = es')
    (* TransformStmt *)
    (fun M F s F' s' (h : TransformStmt M F s F' s') =>
      StmtNoMacroInvocations s F M ->
      s = s')
    ); intros; auto.
  - (* ParenExpr *)
    f_equal. inversion_clear H0; auto.
  - (* UnExpr *)
    f_equal. inversion_clear H0; auto.
  - (* BinExpr *)
    inversion_clear H1.
    f_equal; auto.
    apply H0. subst F'.
    apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations;
      auto.
  - (* Assign *)
    inversion_clear H0. f_equal; auto.
  - (* Function call *)
    inversion_clear H2. f_equal; auto.
  - (* Macro invocation (contradiction) *)
    inversion_clear H0.  apply StringMap_mapsto_in in m. contradiction.
  - (* Macro invocation (contradiction) *)
    inversion_clear H0.  apply StringMap_mapsto_in in m. contradiction.
  - (* ExprList *)
    inversion_clear H1. f_equal; auto.
    apply ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations with
      (F':=Feresult) in H3; auto. rewrite <- e0 in H3. auto.
  - inversion_clear H0. f_equal; auto.
  - inversion_clear H2. f_equal; auto.
    + apply H0. rewrite e.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
    + apply H1. rewrite e0. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
      rewrite e. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
  - inversion_clear H2. f_equal; auto.
    apply H0. rewrite e. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
  - inversion_clear H1. f_equal; auto. f_equal; auto.
    assert (Compound ss = Compound ss').
    { apply H0. rewrite e.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto. }
    inversion H1. auto.
Qed.


(*  If an expression does not contain macro invocations, then after
    transformation it does not contain macro invocations *)
Lemma TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations : forall M F e F' e',
  TransformExpr M F e F' e' ->
  ExprNoMacroInvocations e F M ->
  ExprNoMacroInvocations e' F' M.
Proof.
  apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
      ExprNoMacroInvocations e F M ->
      ExprNoMacroInvocations e' F' M)
    (* TransformExprList *)
    (fun M F es F' es' (h : TransformExprList M F es F' es') =>
      ExprListNoMacroInvocations es F M ->
      ExprListNoMacroInvocations es' F' M)
    (* TransformStmt *)
    (fun M F s F' s' (h : TransformStmt M F s F' s') =>
      StmtNoMacroInvocations s F M ->
      StmtNoMacroInvocations s' F' M)); intros; auto.
  - (* ParenExpr *)
    inversion_clear H0. constructor; auto.
  - (* UnExpr *)
    inversion_clear H0. constructor; auto.
  - (* BinExpr *)
    inversion_clear H1. constructor; auto.
    + subst F''.
      apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations;
        auto.
    + apply H0.
      subst F'.
      apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations;
        auto.
  - (* Assign *)
    inversion_clear H0. constructor; auto.
  - (* Function call *)
    inversion_clear H2.
    assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
    { apply StringMapFacts.MapsTo_fun with F x; auto. }
    inversion H2; subst params0 fstmt0 fexpr0; clear H2.
    apply NM_CallOrInvocation with params fstmt' fexpr'; auto.
    + (* Prove that transformed arguments don't contain macro invocations *)
      subst F''''. apply ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations; auto.
      subst F'''. apply ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations; auto.
      subst F''. apply ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations; auto.
    + (* Prove that the function can actually be found in the tranformed
         function table *)
      subst F'''' newdef. apply StringMapFacts.add_mapsto_iff.
      left. auto.
    +
      rewrite e10.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
      rewrite e1. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
      apply H0.
      rewrite e. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
    + (* Prove that the transformed function expression does not contain
         macro invocations *)
      subst F''''. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
      apply H1.
      subst F''. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
      subst F'. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
  - (* Macro invocation 
    (can't happen since we are assuming no macro invocations *)
    intros. inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - (* Macro invocation 
    (can't happen since we are assuming no macro invocations *)
    intros. inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - (* ExprList *)
    intros. inversion_clear H1. constructor; auto.
    + subst F''. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
    + apply H0. rewrite e0.
      apply ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations; auto.
  - inversion_clear H0. constructor; auto.
  - inversion_clear H2. constructor.
    + rewrite e1. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
      rewrite e0. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
    + rewrite e1. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
      apply H0. rewrite e.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
    + apply H1. rewrite e0.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
      rewrite e. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
  - inversion_clear H2. constructor; auto.
    + rewrite e0. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
    + apply H0. rewrite e.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
  - inversion_clear H1. constructor.
    + rewrite e0. apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
    + apply H0. rewrite e.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto.
Qed.
