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
  MapTheorems
  NoCallsFromFunctionTable
  NoMacroInvocations
  NoVarsInEnvironment.


Inductive TransformExpr :
  macro_table -> function_table -> expr ->
  function_table -> expr -> Prop :=

  | Transform_Num : forall M F z,
    TransformExpr M F (Num z) F (Num z)

  | Transform_Var : forall M F x,
    TransformExpr M F (Var x) F (Var x)

  | Transform_ParenExpr : forall M F e0 F' e0',
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (ParenExpr e0) F' (ParenExpr e0')

  | Transform_UnExpr : forall M F e0 F' e0' uo,
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (UnExpr uo e0) F' (UnExpr uo e0')

  | Transform_BinExpr : forall bo M F e1 e2 F' F'' F1result F2result e1' e2',

    (* Transform the left operand *)
    TransformExpr M F e1 F' e1' ->
    F' = StringMapProperties.update F F1result ->

    (* Transform the right operand *)
    TransformExpr M F' e2 F'' e2' ->
    F'' = StringMapProperties.update F' F2result ->

    (* None of the function calls in e1 are to functions that were added
       while transforming e2 *)
    ExprNoCallsFromFunctionTable e1 F M F2result ->
    (* None of the functions calls in e1' are to functions that were added
       while transforming e2 *)
    ExprNoCallsFromFunctionTable e1' F' M F2result ->
    (* None of the functions calls in e2 are to functions that were added
       while transforming e1 *)
    ExprNoCallsFromFunctionTable e2 F M F1result ->
    (* None of the functions calls in e2' are to functions that were added
       while transforming e1 *)
    ExprNoCallsFromFunctionTable e2' F'' M F1result ->

    (* This is interesting - In order for the proof to succeed, we must assert that
     both the left and right transformations result in ultimately the same function
     table. This is what we do in our unification step.
     This looks funny, but it makes sense when we consider the fact that our
     transformation is defined in "big-step" notation - that is, we are not concerned
     with the intermediate results, just that the final function table between these
     two operands should be equal. If we were to define the semantics using small-step
     notation, then we would have to transform each operand one at a time *)

    TransformExpr M F (BinExpr bo e1 e2) F'' (BinExpr bo e1' e2')

  | Transform_Assign : forall M F x e F' e',
    TransformExpr M F e F' e' ->
    TransformExpr M F (Assign x e) F' (Assign x e')

  | Transform_FunctionCall :
    forall   F M x es F' es'
             params fstmt fexpr fstmt' fexpr',

    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->

    (* Transform function arguments *)
    TransformArgs M F es F' es' ->

    (* Transform function statement *)
    TransformStmt M F fstmt F' fstmt' ->

    (* Transform function return expression *)
    TransformExpr M F fexpr F' fexpr' ->

    (* Add the transformed function back to the function table under a new name *)
    F' = StringMap.add x (params, fstmt', fexpr') F ->

    TransformExpr M F (CallOrInvocation x es) F' (CallOrInvocation x es')

  | Transform_ObjectLikeMacroNoSideEffectsNoSharedVarsNoNestedMacros :
    forall F M x F' params mexpr mexpr' fname,
    StringMap.MapsTo x (params, mexpr) M ->

    (* The macro does not have side-effects *)
    ~ ExprHasSideEffects mexpr ->
    (* The macro does not contain nested macro invocations *)
    ExprNoMacroInvocations mexpr F M ->
    (* The macro does not share variables with the caller environment *)
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x nil) v S' ->
      ExprNoVarsInEnvironment mexpr E) ->
    (* Transform macro body *)
    TransformExpr M F mexpr F' mexpr' ->

    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F ->
    F' = StringMap.add fname (nil, Skip, mexpr') F ->

    TransformExpr M F (CallOrInvocation x nil) F' (CallOrInvocation fname nil)
with TransformArgs :
  macro_table -> function_table -> list expr ->
  function_table -> list expr -> Prop :=

  (* End of arguments *)
  | TransformArgs_Nil : forall M F,
    TransformArgs M F nil F nil

  (* There are arguments left to transform *)
  | TransformArgs_Cons : forall M F e es F' e' es',
    (* Transform the first expression *)
    TransformExpr M F e F' e' ->

    (* Transform the remaining expressions *)
    TransformArgs M F es F' es' ->

    TransformArgs M F (e::es) F' (e'::es')
with TransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=

  | Transform_Skip : forall M F,
    TransformStmt M F Skip F Skip.


Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformArgs_mut := Induction for TransformArgs Sort Prop
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
  -
    simpl in H. apply Classical_Prop.not_or_and in H. destruct H.
    unfold ExprHasSideEffects. fold ExprHasSideEffects.
    apply Classical_Prop.and_not_or. split; auto.
Qed.


Lemma not_ExprHasSideEffects_TransformArgs_Forall_not_ExprHasSideEffects : forall es,
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  forall M F F' es',
    TransformArgs M F es F' es' ->
  Forall (fun e => ~ ExprHasSideEffects e) es'.
Proof.
  intros. induction H0.
  - auto.
  - inversion H. subst. apply Forall_cons.
    * apply not_ExprHasSideEffects_TransformExpr_not_ExprHasSideEffects with e M F F'; auto.
    * apply IHTransformArgs; auto.
Qed.


(* This proof is easy right now because we only have Skip statements *)
Lemma EvalStmt_TransformArgs_EvalStmt : forall S E G F M stmt S' F' stmt',
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
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
      NoMacroInvocationsArgs es F M ->
      es = es')
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
      True (* TODO: Fix this later once we add more statements *))); intros; auto.
  -
    f_equal. inversion_clear H0; auto.
  -
    f_equal. inversion_clear H0; auto.
  -
    inversion_clear H1.
    f_equal; auto.
    apply H0. subst F'.
    apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations;
      auto.
  -
    inversion_clear H0. f_equal; auto.
  -
    inversion_clear H2. f_equal; auto.
  -
    inversion_clear H0.  apply StringMap_mapsto_in in m. contradiction.
  -
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
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
      NoMacroInvocationsArgs es F M ->
      NoMacroInvocationsArgs es' F' M)
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
      True (* TODO: Fix this later once we add more statements *))); intros; auto.
  - inversion_clear H0. constructor; auto.
  - inversion_clear H0. constructor; auto.
  - inversion_clear H1. constructor; auto.
    + subst F''.
      apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations;
        auto.
    + apply H0.
      subst F'.
      apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations;
        auto.
  - inversion_clear H0. constructor; auto.
  - inversion_clear H2. 
    assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
    { apply StringMapFacts.MapsTo_fun with F x; auto. }
    inversion H2; subst params0 fstmt0 fexpr0; clear H2.
    apply NM_CallOrInvocation with params fstmt' fexpr'; auto.
    subst F'. apply StringMapFacts.add_mapsto_iff. auto.
  - intros. inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - intros. inversion_clear H1. constructor; auto.
Qed.


Lemma TransformArgs_ExprNoMacroInvocationsArgs_e_eq: forall M F es F' es',
  TransformArgs M F es F' es' ->
  NoMacroInvocationsArgs es F M ->
  es = es'.
Proof.
  intros. induction H; auto.
  inversion_clear H0. f_equal; auto.
  eapply TransformExpr_ExprNoMacroInvocations_e_eq; eauto.
Qed.


Lemma TransformArgs_NoMacroInvocationsArgs_NoMacroInvocationsArgs : forall M F es F' es',
  TransformArgs M F es F' es' ->
  NoMacroInvocationsArgs es F M ->
  NoMacroInvocationsArgs es' F' M.
Proof.
  apply (TransformArgs_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
      ExprNoMacroInvocations e F M ->
      ExprNoMacroInvocations e' F' M)
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
      NoMacroInvocationsArgs es F M ->
      NoMacroInvocationsArgs es' F' M)
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
      True (* TODO: Fix this later once we add more statements *))); intros; auto.
  - inversion_clear H0. constructor; auto.
  - inversion_clear H0. constructor; auto.
  - inversion_clear H1. constructor.
    +
      subst F''.
      apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations;
        auto.
    +
      subst F''.
      apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations with
        (F':=F1result) in H3; auto.
      rewrite <- e in H3. auto.
  - inversion_clear H0. constructor; auto.
  - inversion_clear H2. econstructor; auto.
    + rewrite e. apply StringMapFacts.add_mapsto_iff. left; auto.
    + apply H1.
      assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion_clear H2. auto.
  - inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - inversion_clear H1. constructor; auto.
Qed.