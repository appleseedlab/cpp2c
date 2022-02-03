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
  induction E1.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHE1. apply H.
  - apply IHE1. apply H.
  - unfold ExprHasSideEffects in H. fold ExprHasSideEffects in H.
    apply Classical_Prop.not_or_and in H.
    rewrite <- IHE1_1 in IHE1_2.
    apply IHE1_2.  apply H. apply H.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Lemma not_ExprHasSideEffects_S_eq: forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  S = S'.
Proof.
  intros e H S E G F M v S' E1.
  induction E1.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHE1. apply H.
  - apply IHE1. apply H.
  - unfold ExprHasSideEffects in H. fold ExprHasSideEffects in H.
    apply Classical_Prop.not_or_and in H.
    rewrite <- IHE1_1 in IHE1_2.
    apply IHE1_2.  apply H. apply H.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Lemma not_ExprHasSideEffects_EvalExpr_EvalExpr : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  EvalExpr S E G F M e v S.
Proof.
  intros e H S E G F M v S' E1.
  induction E1.
  - apply E_Num.
  - apply E_LocalVar with l; assumption.
  - apply E_GlobalVar with l; assumption.
  - apply E_ParenExpr. apply IHE1. assumption.
  - apply E_UnExpr. apply IHE1. assumption.
  - unfold ExprHasSideEffects in H. fold ExprHasSideEffects in H.
    apply Classical_Prop.not_or_and in H. destruct H. apply E_BinExpr with S'.
    + assumption.
    + apply not_ExprHasSideEffects_S_eq in E1_1.
      * subst. apply IHE1_2. assumption.
      * assumption.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Theorem Forall_not_ExprHasSideEffects_EvalArgs_S_Equal : forall S E G F M ps es S' vs Ef Sargs l,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  NatMap.Equal S S'.
Proof.
  intros. induction H0.
  - reflexivity.
  - inversion H. apply not_ExprHasSideEffects_S_eq in H0.
    rewrite H0. apply IHEvalArgs. assumption. assumption.
Qed.


Theorem Forall_not_ExprHasSideEffects_EvalArgs_S_eq : forall S E G F M ps es S' vs Ef Sargs l,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  S = S'.
Proof.
  intros. induction H0.
  - reflexivity.
  - inversion H. apply not_ExprHasSideEffects_S_eq in H0.
    rewrite H0. apply IHEvalArgs. assumption. assumption.
Qed.


Lemma Forall_not_ExprHasSideEffects_EvalArgs_EvalArgs: forall S E G F M ps es S' vs Ef Sargs l,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  EvalArgs S E G F M ps es vs S Ef Sargs l.
Proof.
  intros. induction H0.
  - apply EvalArgs_nil.
  - inversion H; subst. apply EvalArgs_cons with Snext; auto.
    + apply not_ExprHasSideEffects_S_eq in H0; subst; auto.
Qed.


Lemma Skip_S_Equal : forall S E G F M S',
  EvalStmt S E G F M Skip S' ->
  NatMap.Equal S S'.
Proof.
  intros. induction H. reflexivity.
Qed.


Lemma Skip_S_eq : forall S E G F M S',
  EvalStmt S E G F M Skip S' ->
  S = S'.
Proof.
  intros. induction H. reflexivity.
Qed.


Lemma not_ExprHasSideEffects_msub_not_ExprHasSideEffects : forall mexpr p e,
  ~ ExprHasSideEffects mexpr ->
  ~ ExprHasSideEffects e ->
  ~ ExprHasSideEffects (msub p e mexpr).
Proof.
  induction mexpr; auto.
  - (* Var *)
    intros. simpl in *. destruct ((p =? x)%string); auto.
  - (* BinExpr *)
    intros. simpl in *. apply Classical_Prop.not_or_and in H. destruct H.
    apply Classical_Prop.and_not_or. split; auto.
  - (* Assign *)
    intros. simpl in *. contradiction.
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

