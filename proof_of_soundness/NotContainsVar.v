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


Lemma ExprNotContainsVar_MSub_no_change: forall mexpr p,
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