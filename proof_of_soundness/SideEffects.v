(*  SideEffects.v
    Definitions for functions checking whether or not a given
    expression has side-effects, and some lemmas related to them
*)

Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  Syntax.


(*  Checks if an expression has side-effects and returns a Boolean
    indicating the result *)
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


(*  Checks if an expression has side-effects and returns Prop indicating
    the result *)
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


(*  Proof of equivalence between the two functions for checking whether
    an expression has side-effects in the positive case *)
Lemma expr_has_side_effects_ExprHasSideEffects_iff : forall e,
  expr_has_side_effects e = true <-> ExprHasSideEffects e.
Proof.
  split; induction e; intros; simpl in *;
    try discriminate; try (apply IHe; apply H);
    try apply I; try contradiction; try reflexivity.
  - apply Bool.orb_prop in H. tauto.
  - apply Bool.orb_true_iff. tauto.
Qed.

(*  Proof of equivalence between the two functions for checking whether
    an expression has side-effects in the negative case *)
Lemma expr_side_effects_not_true_not_ExprHasSideEffects_iff : forall e,
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


(*  If an expression does not have side-effects, and terminates to some
    value and final store under some context, then the final store
    is equal to the initial store *)
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


(*  If a Skip statement terminates under some context, then
    the initial store the Skip statement was evaluated under
    is equal to the final store it evaluates to *)
Lemma Skip_S_Equal : forall S E G F M S',
  EvalStmt S E G F M Skip S' ->
  NatMap.Equal S S'.
Proof.
  intros. inversion_clear H. auto.
Qed.


(*  If an expression does not have side-effects, and substitute into it a single
    expression which also does not have side-effects, then the fully-
    substituted expression will also not have side-effects *)
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


(*  If an expression does not have side-effects, and substitute into it
    multiple expression which also do not have side-effects, then the
    fully-substituted expression will also not have side-effects *)
Lemma not_ExprHasSideEffects_MacroSubst_not_ExprHasSideEffects : forall mexpr params es ef,
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

