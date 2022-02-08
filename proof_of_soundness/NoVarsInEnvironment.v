(*  NoVarsInEnvironment.v
    Definition of a relation in which a given expression contains no
    variables in a given environment *)

Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  Syntax.

(*  Definition of the relation *)
Inductive ExprNoVarsInEnvironment : expr -> environment -> Prop :=
  | NV_Num : forall z E,
    (*  Numerals of course do not contain a variable *)
    ExprNoVarsInEnvironment (Num z) E
  | NV_Var : forall x E,
    (*  The variable is not in the given environment *)
    ~ StringMap.In x E ->
    ExprNoVarsInEnvironment (Var x) E
  | NV_ParenExpr : forall e0 E,
    (*  The inner expression does not contain any variable
        in the given environment *)
    ExprNoVarsInEnvironment e0 E ->
    ExprNoVarsInEnvironment (ParenExpr e0) E
  | NV_UnExpr : forall uo e0 E,
    (*  The inner expression does not contain any variable
        in the given environment *)
    ExprNoVarsInEnvironment e0 E ->
    ExprNoVarsInEnvironment (UnExpr uo e0) E
  | NV_Bin_Expr : forall bo e1 e2 E,
    (*  The left operand does not contain any variable
        in the given environment *)
    ExprNoVarsInEnvironment e1 E ->
    (*  The right operand does not contain any variable
        in the given environment *)
    ExprNoVarsInEnvironment e2 E ->
    ExprNoVarsInEnvironment (BinExpr bo e1 e2) E
  | NV_Assign : forall x e0 E,
    (*  The LHS of the assignment is not in the given environment *)
    ~ StringMap.In x E ->
    (*  The inner expression does not contain any variable
        in the given environment *)
    ExprNoVarsInEnvironment e0 E ->
    ExprNoVarsInEnvironment (Assign x e0) E
  | NV_CallOrInvocation : forall x es E,
    (*  None of the arguments contain a variable
        in the given environment *)
    ExprListNoVarsInEnvironment es E ->
    ExprNoVarsInEnvironment (CallOrInvocation x es) E
with ExprListNoVarsInEnvironment : list expr -> environment -> Prop :=
  | NV_ExprList_nil : forall E,
    (*  An empty expression list does not contain a variable *)
    ExprListNoVarsInEnvironment nil E
  | NV_ExprList_cons : forall e es E,
    (*  The head of the list does not contain a variable in the
        given environment *)
    ExprNoVarsInEnvironment e E ->
    (*  The tail of the list does not contasin a variable in the
        given environment *)
    ExprListNoVarsInEnvironment es E ->
    ExprListNoVarsInEnvironment (e::es) E.
