(*  Constant.v
    Definition for expressions which only contain constant terms
    (i.e., numerals), and some lemmas concerning them
*)

From Cpp2C Require Import
  Syntax
  ConfigVars
  EvalRules.

(*  Definition of constant expressions *)
Fixpoint ExprConstant (e : expr) : Prop :=
  match e with
  | Num z => True
  | Var x => False
  | ParenExpr e0 => ExprConstant e0
  | UnExpr uo e0 => ExprConstant e0
  | BinExpr bo e1 e2 => ExprConstant e1 /\ ExprConstant e2
  | Assign x e0 => False
  | CallOrInvocation x es => False
end.


(*  If a given expression is a constant expression, then it will evaluate
    to the same value under all contexts *)
Lemma ExprConstant_EvalExpr : forall e,
  ExprConstant e ->
  forall S1 E1 G1 F1 M1 v1 S'1,
  EvalExpr S1 E1 G1 F1 M1 e v1 S'1 ->
  forall S2 E2 G2 F2 M2 v2 S'2,
  EvalExpr S2 E2 G2 F2 M2 e v2 S'2 ->
  v1 = v2.
Proof.
  intros e H S1 E1 G1 F1 M1 v1 S'1 H0. induction H0; intros; try contradiction.
  - inversion_clear H1; auto.
  - inversion_clear H1. eauto.
  - inversion H1. subst. assert (v = v0). { eauto. }
    subst. auto.
  - inversion_clear H. inversion H0. subst.
    assert (v1 = v3). { eauto. }
    assert (v2 = v4). { eauto. }
    subst. auto.
Qed.


(*  Constant expressions do not change the store when evaluated *)
Lemma ExprConstant_EvalExpr_S_Equal : forall e,
  ExprConstant e ->
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  NatMap.Equal S S'.
Proof.
  intros. induction H0; auto; try contradiction.
  - inversion H. rewrite IHEvalExpr1; auto.
Qed.


(*  If a given expression is a constant expression, then it can
    be evaluated as Num instead (constant folding) *)
Lemma ExprConstant_EvalExpr_EvalExpr_Num : forall e,
  ExprConstant e ->
  forall S1 E1 G1 F1 M1 v1 S'1,
  EvalExpr S1 E1 G1 F1 M1 e v1 S'1 ->
  EvalExpr S1 E1 G1 F1 M1 (Num v1) v1 S'1.
Proof.
  intros e H S1 E1 G1 F1 M1 v1 S'1 H0. induction H0; intros; try contradiction.
  - constructor; auto.
  - auto.
  - constructor. apply ExprConstant_EvalExpr_S_Equal in H0; auto.
  - inversion_clear H. constructor.
    apply ExprConstant_EvalExpr_S_Equal in H0_, H0_0; auto.
    rewrite H0_. auto.
Qed.
