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


(*  Relation only holds if an expression does not reference any function in the
    given function table *)
Definition ExprNoCallsFromFunctionTable (e : expr) (F' : function_table) :=
  forall S E G F M v S',
  EvalExpr S E G F M e v S' <->
  EvalExpr S E G (StringMapProperties.update F F') M e v S'.


(*  Relation only holds if a statement does not reference any function in the
    given function table *)
Definition StmtNoCallsFromFunctionTable (s : stmt) (F' : function_table) :=
  forall S E G F M S',
  EvalStmt S E G F M s S' <->
  EvalStmt S E G (StringMapProperties.update F F') M s S'.


(*  Relation only holds if an expression list does not reference any function
    in the given function table *)
Definition ExprListNoCallsFromFunctionTable (es : list expr) (F' : function_table) :=
  forall S E G F M S' es',
  EvalExprList S E G F M es S' es' <->
  EvalExprList S E G (StringMapProperties.update F F') M es S' es'.