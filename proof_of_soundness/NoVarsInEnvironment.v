(*  NoCallsFromFunctionTable.v
    Definition for relation stating that an expression does not contain any
    calls to a function from the given function table
*)

Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  Syntax.


(*  Relation only holds if an expression does not reference any var in the
    given local environment *)
Definition ExprNoVarsInLocalEnvironment (e : expr) (E' : environment) :=
  forall S E G F M v S',
  EvalExpr S E G F M e v S' <->
  EvalExpr S (StringMapProperties.update E E') G F M e v S'.