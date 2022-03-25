(*  Constant.v
    Definition for expressions which only contain constant terms
    (i.e., numerals), and some lemmas concerning them
*)

From Cpp2C Require Import
  Syntax
  ConfigVars
  EvalRules.

Definition ExprConstant (e : expr) :=
  forall S1 E1 G1 F1 M1 v1 S'1,
  EvalExpr S1 E1 G1 F1 M1 e v1 S'1 ->
  forall S2 E2 G2 F2 M2 v2 S'2,
  EvalExpr S2 E2 G2 F2 M2 e v2 S'2 ->
  v1 = v2 /\ NatMap.Equal S'1 S'2.