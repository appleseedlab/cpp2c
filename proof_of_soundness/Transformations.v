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

  | Transform_ObjectLikeMacroNoSideEffectsNoSharedVarsNoNestedMacros :
    forall F M x F' params mexpr mexpr' fname newdef,

    StringMap.MapsTo x (params, mexpr) M ->

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
  | TransformExprList_Cons : forall M F e es F' e' es',
    (* Transform the first expression *)
    TransformExpr M F e F' e' ->

    (* Transform the remaining expressions *)
    TransformExprList M F es F' es' ->

    TransformExprList M F (e::es) F' (e'::es')
with TransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=

  | Transform_Skip : forall M F,
    TransformStmt M F Skip F Skip.


Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformExprList_mut := Induction for TransformExprList Sort Prop
with TransformStmt_mut := Induction for TransformStmt Sort Prop.


(* This proof is easy right now because we only have Skip statements *)
Lemma mapsto_TransformStmt_mapsto : forall x fdef F M stmt F' stmt', 
  StringMap.MapsTo x fdef F ->
  TransformStmt M F stmt F' stmt' ->
  StringMap.MapsTo x fdef F'.
Proof.
  intros. induction H0. assumption.
Qed.


Lemma not_ExprHasSideEffects_TransformExpr_not_ExprHasSideEffects : forall e,
  ~ ExprHasSideEffects e ->
  forall M F F' e',
    TransformExpr M F e F' e' ->
    ~ ExprHasSideEffects e'.
Proof.
  intros. induction H0; auto.
  - (* BinExpr *)
    simpl in H. apply Classical_Prop.not_or_and in H. destruct H.
    unfold ExprHasSideEffects. fold ExprHasSideEffects.
    apply Classical_Prop.and_not_or. split; auto.
Qed.


Lemma not_ExprHasSideEffects_TransformExprList_Forall_not_ExprHasSideEffects : forall es,
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  forall M F F' es',
    TransformExprList M F es F' es' ->
  Forall (fun e => ~ ExprHasSideEffects e) es'.
Proof.
  intros. induction H0.
  - (* nil *)
    auto.
  - (* cons *)
    inversion H. subst. constructor; auto.
    (* Prove the head of the list doesn't have side-effects *)
    apply not_ExprHasSideEffects_TransformExpr_not_ExprHasSideEffects with e M F F'; auto.
Qed.


(* This proof is easy right now because we only have Skip statements *)
Lemma EvalStmt_TransformExprList_EvalStmt : forall S E G F M stmt S' F' stmt',
  EvalStmt S E G F M stmt S' ->
  TransformStmt M F stmt F' stmt' ->
  EvalStmt S E G F' M stmt S'.
Proof.
  intros. induction H0. assumption.
Qed.


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
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
      True (* TODO: Fix this later once we add more statements *))); intros; auto.
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
  - (* ExprList *)
    inversion_clear H1. f_equal; auto.
Qed.


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
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
      True (* TODO: Fix this later once we add more statements *))); intros; auto.
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
      subst F''''. apply ExprListNoMacroInvocations_update_ExprNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations; auto.
      subst F'''. apply ExprListNoMacroInvocations_update_ExprNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations; auto.
      subst F''. apply ExprListNoMacroInvocations_update_ExprNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations; auto.
    + (* Prove that the function can actually be found in the tranformed
         function table *)
      subst F'''' newdef. apply StringMapFacts.add_mapsto_iff.
      left. auto.
    + (* Prove that the transformed function expression does not contain
         macro invocations *)
      subst F''''. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
      apply H1.
      subst F''. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
      subst F'. apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto.
  - (* Macro invocation 
    (can't happen since we are assuming no macro invocations *)
    intros. inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - (* ExprList *)
    intros. inversion_clear H1. constructor; auto.
Qed.


Lemma TransformExprList_ExprExprListNoMacroInvocations_e_eq: forall M F es F' es',
  TransformExprList M F es F' es' ->
  ExprListNoMacroInvocations es F M ->
  es = es'.
Proof.
  intros. induction H; auto.
  inversion_clear H0. f_equal;
    eauto using TransformExpr_ExprNoMacroInvocations_e_eq.
Qed.


Lemma TransformExprList_ExprListNoMacroInvocations_ExprListNoMacroInvocations : forall M F es F' es',
  TransformExprList M F es F' es' ->
  ExprListNoMacroInvocations es F M ->
  ExprListNoMacroInvocations es' F' M.
Proof.
  intros. induction H.
  - (* nil *)
    constructor.
  - (* cons *)
    inversion_clear H0. constructor;
      eauto using TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations.
Qed.
