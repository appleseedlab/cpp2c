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


(*  An expression without side-effects is one which does
    not modify its input store when evaluated *)
Definition ExprNoSideEffects (e : expr) :=
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  NatMap.Equal S S'.


(*  A store without side side-effects is one which does
    not modify its input store when evaluated *)
Definition ExprListNoSideEffects (es : list expr) :=
  forall S E G F M S' es',
  EvalExprList S E G F M es S' es' ->
  NatMap.Equal S S'.