Require Import
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  EvalRules.


Inductive TransformExpr :
  macro_table -> function_table -> expr ->
  function_table -> expr -> Prop :=

  | Transform_Num : forall M F z,
    TransformExpr M F (Num z) F (Num z)

  | Transform_Var : forall M F x,
    TransformExpr M F (Var x) F (Var x)

  | Transform_ParenExpr : forall M F e0 F' e0',
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (ParenExpr e0) F' (ParenExpr e0')

  | Transform_UnExpr : forall M F e0 F' e0' uo,
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (UnExpr uo e0) F' (UnExpr uo e0')

  | Transform_BinExpr : forall bo M F e1 e2 F' F'' F1result F2result e1' e2',

    (* Transform the left operand *)
    TransformExpr M F e1 F' e1' ->
    F' = StringMapProperties.update F F1result ->

    (* Transform the right operand *)
    TransformExpr M F' e2 F'' e2' ->
    F'' = StringMapProperties.update F' F2result ->

    (* None of the function calls in e1 are to functions that were added
       while transforming e2 *)
    ExprNoCallsFromFunctionTable e1 F M F2result ->
    (* None of the functions calls in e1' are to functions that were added
       while transforming e2 *)
    ExprNoCallsFromFunctionTable e1' F' M F2result ->
    (* None of the functions calls in e2 are to functions that were added
       while transforming e1 *)
    ExprNoCallsFromFunctionTable e2 F M F1result ->
    (* None of the functions calls in e2' are to functions that were added
       while transforming e1 *)
    ExprNoCallsFromFunctionTable e2' F'' M F1result ->

    (* This is interesting - In order for the proof to succeed, we must assert that
     both the left and right transformations result in ultimately the same function
     table. This is what we do in our unification step.
     This looks funny, but it makes sense when we consider the fact that our
     transformation is defined in "big-step" notation - that is, we are not concerned
     with the intermediate results, just that the final function table between these
     two operands should be equal. If we were to define the semantics using small-step
     notation, then we would have to transform each operand one at a time *)

    TransformExpr M F (BinExpr bo e1 e2) F'' (BinExpr bo e1' e2')

  | Transform_Assign : forall M F x e F' e',
    TransformExpr M F e F' e' ->
    TransformExpr M F (Assign x e) F' (Assign x e')

  | Transform_FunctionCall :
    forall   F M x es F' es'
             params fstmt fexpr fstmt' fexpr',

    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->

    (* Transform function arguments *)
    TransformArgs M F es F' es' ->

    (* Transform function statement *)
    TransformStmt M F fstmt F' fstmt' ->

    (* Transform function return expression *)
    TransformExpr M F fexpr F' fexpr' ->

    (* Add the transformed function back to the function table under a new name *)
    F' = StringMap.add x (params, fstmt', fexpr') F ->

    TransformExpr M F (CallOrInvocation x es) F' (CallOrInvocation x es')

  | Transform_ObjectLikeMacroNoSideEffectsNoSharedVarsNoNestedMacros :
    forall F M x F' params mexpr mexpr' fname,
    StringMap.MapsTo x (params, mexpr) M ->

    (* The macro does not have side-effects *)
    ~ ExprHasSideEffects mexpr ->
    (* The macro does not contain nested macro invocations *)
    NoMacroInvocations mexpr F M ->
    (* The macro does not share variables with the caller environment *)
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x nil) v S' ->
      NoVarsInEnvironment mexpr E) ->
    (* Transform macro body *)
    TransformExpr M F mexpr F' mexpr' ->

    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F ->
    F' = StringMap.add fname (nil, Skip, mexpr') F ->

    TransformExpr M F (CallOrInvocation x nil) F' (CallOrInvocation fname nil)
with TransformArgs :
  macro_table -> function_table -> list expr ->
  function_table -> list expr -> Prop :=

  (* End of arguments *)
  | TransformArgs_Nil : forall M F,
    TransformArgs M F nil F nil

  (* There are arguments left to transform *)
  | TransformArgs_Cons : forall M F e es F' e' es',
    (* Transform the first expression *)
    TransformExpr M F e F' e' ->

    (* Transform the remaining expressions *)
    TransformArgs M F es F' es' ->

    TransformArgs M F (e::es) F' (e'::es')
with TransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=

  | Transform_Skip : forall M F,
    TransformStmt M F Skip F Skip.

