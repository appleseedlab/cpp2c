Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  Syntax.


(* This just has to check syntax *)
Inductive ExprNotContainsVar : expr -> string -> Prop :=
  | NCV_Num : forall z x,
    ExprNotContainsVar (Num z) x
  | NCV_Var : forall x y,
    x <> y ->
    ExprNotContainsVar (Var y) x
  | NCV_ParenExpr : forall e0 x,
    ExprNotContainsVar e0 x ->
    ExprNotContainsVar (ParenExpr e0) x
  | NCV_UnExpr : forall uo e0 x,
    ExprNotContainsVar e0 x ->
    ExprNotContainsVar (UnExpr uo e0) x
  | NCV_Bin_Expr : forall bo e1 e2 x,
    ExprNotContainsVar e1 x ->
    ExprNotContainsVar e2 x ->
    ExprNotContainsVar (BinExpr bo e1 e2) x
  | NCV_Assign : forall x y e0,
    x <> y ->
    ExprNotContainsVar e0 x ->
    ExprNotContainsVar (Assign y e0) x
  | NCV_CallOrInvocation : forall x es,
    ExprListNotContainsVar es x ->
    ExprNotContainsVar (CallOrInvocation x es) x
with ExprListNotContainsVar : list expr -> string -> Prop :=
  | NCV_nil : forall x,
    ExprListNotContainsVar nil x
  | NCV_cons : forall e es x,
    ExprNotContainsVar e x ->
    ExprListNotContainsVar es x ->
    ExprListNotContainsVar (e::es) x.


Scheme ExprNotContainsVar_mut := Induction for ExprNotContainsVar Sort Prop
with ExprListNotContainsVar_mut := Induction for ExprListNotContainsVar Sort Prop.


Lemma foo: forall mexpr p,
  ExprNotContainsVar mexpr p ->
  forall e,
  MSub p e mexpr mexpr.
Proof.
  apply (ExprNotContainsVar_mut
    (fun mexpr p (h : ExprNotContainsVar mexpr p) =>
      forall e,
      MSub p e mexpr mexpr)
    (fun es p ( h : ExprListNotContainsVar es p) =>
      forall e,
      MSubList p e es es)).
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - intros. apply MS_Assign_No_Replace; auto.
  - intros. apply MS_Call_Or_Invocation; auto.
  - constructor.
  - constructor; auto.
Qed.


Lemma MSub_ef_eq_e_or_mexpr_eq_ef: forall p e mexpr ef,
  MSub p e mexpr ef ->
  ((mexpr = Var p /\ ef = e) \/
    forall x e0 e0',
    p = x ->
    mexpr = Assign p e0 ->
    e = Var x ->
    MSub p e e0 e0' ->
    ef = Assign x e0' ) \/
  ((ExprNotContainsVar mexpr p) -> mexpr = ef).
Proof.
  intros. induction H.
  - right. intros. auto.
  - left. subst. auto.
  - right. auto.
  - destruct IHMSub.
    + destruct H0.
      * destruct H0. subst. right. intros. inversion_clear H0.
        inversion_clear H1. contradiction.
      * left. right. intros. discriminate.
    + right. intros. f_equal. inversion_clear H1. auto.
 - destruct IHMSub.
    + destruct H0.
      * destruct H0. subst. right. intros. inversion_clear H0.
        inversion_clear H1. contradiction.
      * left.  right. intros. discriminate.
    + right. intros. f_equal. inversion_clear H1. auto.
  - destruct IHMSub1.
    + destruct H1.
      * destruct H1. subst. right. intros. inversion_clear H1.
        inversion_clear H2. contradiction.
      * left. right. intros. discriminate.
    + destruct IHMSub2.
      * destruct H2.
        -- destruct H2. subst. right. intros. inversion_clear H2.
           inversion_clear H4. contradiction.
        -- left. right. intros. discriminate.
      * right. intros. inversion_clear H3. f_equal; auto.
  - destruct IHMSub.
    + destruct H2.
      * destruct H2. right. intros. inversion_clear H4. contradiction.
      * left. right. intros. subst. inversion H5. subst. inversion H4. subst. f_equal.
        apply MSub_deterministic with (ef:=e0'0) in H1; auto.
    + right. intros. subst. inversion_clear H3. contradiction.
  - destruct IHMSub.
    + destruct H1.
      * destruct H1. right. intros. subst. inversion_clear H3.
        inversion_clear H2. contradiction.
      * left. right. intros. inversion H3. subst. contradiction.
    + right. intros. subst. inversion_clear H2. f_equal. auto.
  - left. right. intros. discriminate.
Qed.


Lemma MacroSubst1_ef_eq_mexpr_or_ef_eq_ef: forall p e mexpr ef,
  MacroSubst (p::nil) (e::nil) mexpr ef ->
  ef = mexpr \/ ef = ef.
Proof.
  intros. induction H; auto.
Qed.