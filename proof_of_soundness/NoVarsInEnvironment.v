Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  Syntax.


Inductive ExprNoVarsInEnvironment : expr -> environment -> Prop :=
  | NV_Num : forall z E,
    ExprNoVarsInEnvironment (Num z) E
  | NV_Var : forall x E,
    ~ StringMap.In x E ->
    ExprNoVarsInEnvironment (Var x) E
  | NV_ParenExpr : forall e0 E,
    ExprNoVarsInEnvironment e0 E ->
    ExprNoVarsInEnvironment (ParenExpr e0) E
  | NV_UnExpr : forall uo e0 E,
    ExprNoVarsInEnvironment e0 E ->
    ExprNoVarsInEnvironment (UnExpr uo e0) E
  | NV_Bin_Expr : forall bo e1 e2 E,
    ExprNoVarsInEnvironment e1 E ->
    ExprNoVarsInEnvironment e2 E ->
    ExprNoVarsInEnvironment (BinExpr bo e1 e2) E
  | NV_Assign : forall x e0 E,
    ~ StringMap.In x E ->
    ExprNoVarsInEnvironment e0 E ->
    ExprNoVarsInEnvironment (Assign x e0) E
  | NV_CallOrInvocation : forall x es E,
    ~ StringMap.In x E ->
    ExprListNoVarsInEnvironment es E ->
    ExprNoVarsInEnvironment (CallOrInvocation x es) E
with ExprListNoVarsInEnvironment : list expr -> environment -> Prop :=
  | NV_ExprList_nil : forall E,
    ExprListNoVarsInEnvironment nil E
  | NV_ExprList_cons : forall e es E,
    ExprNoVarsInEnvironment e E ->
    ExprListNoVarsInEnvironment es E ->
    ExprListNoVarsInEnvironment (e::es) E.


Scheme ExprNoVarsInEnvironment_mut := Induction for ExprNoVarsInEnvironment Sort Prop
with ExprListNoVarsInEnvironment_mut := Induction for ExprListNoVarsInEnvironment Sort Prop.


Lemma ExprNoVarsInEnvironment_MSub_ExprNoVarsInEnvironment : forall mexpr E,
  ExprNoVarsInEnvironment mexpr E ->
  forall e,
  ExprNoVarsInEnvironment e E ->
  forall p ef,
  MSub p e mexpr ef ->
  ExprNoVarsInEnvironment ef E.
Proof.
  apply (ExprNoVarsInEnvironment_mut
    (fun mexpr E (h : ExprNoVarsInEnvironment mexpr E) =>
      forall e,
      ExprNoVarsInEnvironment e E ->
      forall p ef,
      MSub p e mexpr ef ->
      ExprNoVarsInEnvironment ef E)
    (fun es E (h : ExprListNoVarsInEnvironment es E) =>
      forall e,
      ExprNoVarsInEnvironment e E ->
      forall p es',
      MSubList p e es es' ->
      ExprListNoVarsInEnvironment es' E)); intros; try constructor; auto.
  - inversion_clear H0; constructor.
  - inversion H0.
    + subst; auto.
    + subst. constructor; auto.
  - inversion_clear H1. constructor. eapply H; eauto.
  - inversion_clear H1. constructor. eapply H; eauto.
  - inversion_clear H2. constructor.
    + eapply H; eauto.
    + eapply H0; eauto.
  - inversion H1. 
    + subst. constructor. inversion H0; auto. eapply H; eauto.
    + subst. constructor; auto. eapply H; eauto.
  - inversion_clear H1. constructor; eauto.
  - inversion_clear H0. constructor.
  - inversion_clear H2. constructor.
    + eapply H; eauto.
    + eapply H0; eauto.
Qed.


Lemma ExprNoVarsInEnvironment_MacroSubst_ExprNoVarsInEnvironment : forall mexpr E,
  ExprNoVarsInEnvironment mexpr E ->
  forall es,
  Forall (fun e => ExprNoVarsInEnvironment e E) es ->
  forall ps ef,
  MacroSubst ps es mexpr ef ->
  ExprNoVarsInEnvironment ef E.
Proof.
  intros. induction H1.
  - auto.
  - inversion_clear H0. apply IHMacroSubst; auto.
    apply ExprNoVarsInEnvironment_MSub_ExprNoVarsInEnvironment with mexpr e p; auto.
Qed.