Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  Syntax.

Fixpoint expr_has_side_effects (e: expr) : bool :=
  match e with
  | Num z => false
  | Var x => false
  | ParenExpr e0 => expr_has_side_effects e0
  | UnExpr uo e0 => expr_has_side_effects e0
  | BinExpr bo e1 e2 =>
    orb (expr_has_side_effects e1) (expr_has_side_effects e2)
  (* This is conservative, but matches the behaviour of Clang *)
  | Assign x e0 => true
  | CallOrInvocation x es => true
end.


Fixpoint ExprHasSideEffects (e : expr) : Prop :=
  match e with
  | Num z => False
  | Var x => False
  | ParenExpr e0 => ExprHasSideEffects e0
  | UnExpr uo e0 => ExprHasSideEffects e0
  | BinExpr bo e1 e2 =>
    (ExprHasSideEffects e1) \/ (ExprHasSideEffects e2)
  (* This is conservative, but matches the behaviour of Clang *)
  | Assign x e0 => True
  | CallOrInvocation x es => True
end.


Theorem expr_has_side_effects_ExprHasSideEffects_iff : forall e,
  expr_has_side_effects e = true <-> ExprHasSideEffects e.
Proof.
  split; induction e; intros; simpl in *;
    try discriminate; try (apply IHe; apply H);
    try apply I; try contradiction; try reflexivity.
  - apply Bool.orb_prop in H. tauto.
  - apply Bool.orb_true_iff. tauto.
Qed.


Theorem expr_side_effects_not_true_not_ExprHasSideEffects_iff : forall e,
  expr_has_side_effects e <> true <-> ~ ExprHasSideEffects e.
Proof.
  split.
  - intros.
    rewrite <- expr_has_side_effects_ExprHasSideEffects_iff.
    unfold not. intros. contradiction.
  - intros. unfold not. intros.
    rewrite <- expr_has_side_effects_ExprHasSideEffects_iff in H.
    contradiction.
Qed.


Lemma not_ExprHasSideEffects_S_Equal : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  NatMap.Equal S S'.
Proof.
  intros e H S E G F M v S' E1.
  induction E1; auto.
  - (* BinExpr *)
    simpl in H. apply Classical_Prop.not_or_and in H. destruct H.
    assert (NatMap.Equal S S'). { auto. }
   rewrite H1. auto.
  - (* Local assignment *)
    unfold ExprHasSideEffects in H. contradiction.
  - (* Global assignment *)
    unfold ExprHasSideEffects in H. contradiction.
  - (* Function call *)
    unfold ExprHasSideEffects in H. contradiction.
  - (* Macro invocation *)
    unfold ExprHasSideEffects in H. contradiction.
Qed.


Theorem Forall_not_ExprHasSideEffects_EvalExprList_S_Equal : forall S E G F M ps es S' vs Ef Sargs l ls,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalExprList S E G F M ps es vs S' Ef Sargs l ls ->
  NatMap.Equal S S'.
Proof.
  intros. induction H0; auto.
  - (* ExprList cons *)
    inversion H. subst x l0.
    apply not_ExprHasSideEffects_S_Equal in H0; auto. rewrite <- H0 in IHEvalExprList.
    auto.
Qed.


Lemma Skip_S_Equal : forall S E G F M S',
  EvalStmt S E G F M Skip S' ->
  NatMap.Equal S S'.
Proof.
  intros. induction H. auto.
Qed.



Lemma not_ExprHasSideEffects_Msub_not_ExprHasSideEffects : forall p e mexpr ef,
  ~ ExprHasSideEffects mexpr ->
  ~ ExprHasSideEffects e ->
    MSub p e mexpr ef ->
  ~ ExprHasSideEffects ef.
Proof.
  intros. induction H1; auto.
  simpl in *. apply Classical_Prop.not_or_and in H. destruct H.
  apply Classical_Prop.and_not_or. auto.
Qed.


Theorem not_ExprHasSideEffects_MacroSubst_not_ExprHasSideEffects : forall mexpr params es ef,
  ~ ExprHasSideEffects mexpr ->
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  MacroSubst params es mexpr ef ->
  ~ ExprHasSideEffects ef.
Proof.
  intros.
  induction H1; auto.
  inversion H0; subst.
  apply IHMacroSubst; eauto using not_ExprHasSideEffects_Msub_not_ExprHasSideEffects.
Qed.

