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
  
  | Transform_BinExpr : forall M F e1 e2 F' F'' e1' e2' bo,
    TransformExpr M F e1 F' e1' ->
    TransformExpr M F e2 F'' e2' ->
    (* If an expression is evaluable under F', then it should be evaluable under F'' *)
    (* There may be a better way to prove this, but I can't figure out how to do it yet *)
    (forall S E G v S', ExprEval S E G F' M e1' v S' -> ExprEval S E G F'' M e1' v S') ->
    TransformExpr M F (BinExpr bo e1 e2) F'' (BinExpr bo e1' e2')
  
  | Transform_Assign : forall M F x e F' e',
    TransformExpr M F e F' e' ->
    TransformExpr M F (Assign x e) F' (Assign x e')

  | Transform_FunctionCall :
    forall   F M x es F' F'' F''' F'''' es'
             params fstmt fexpr fstmt' fexpr',
    (* Macros shadow functions, so to determine if what we are calling is a function
       it suffices just to check that its name is not in the macro table and is in
       the function table *)
    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    
    (* There is only one mapping for x in the original function table *)
    (forall params0 fstmt0 fexpr0 params1 fstmt1 fexpr1,
      StringMap.MapsTo x (params0, fstmt0, fexpr0) F ->
      (params0, fstmt0, fexpr0) = (params1, fstmt1, fexpr1)) ->
    
    (* Transform function arguments first *)
    TransformArgs M F es F' es' ->
    TransformStmt M F' fstmt F'' fstmt' ->
    TransformExpr M F'' fexpr F''' fexpr' ->
    StringMap.Equal F'''' (StringMap.add x (params, fstmt', fexpr') F''') ->
    TransformExpr M F (CallOrInvocation x es) F'''' (CallOrInvocation x es')
    
  | Transform_SideEffectFreeMacro :
    forall  F M x es F' F'' es' params mexpr fname
  
          (S : store) (E : environment) (G : environment)
          (vs : list Z) (ls : list nat) (v : Z) (Ef : environment)
          Sargs S' S'' S''' S'''' S''''',
    (* Again, macros shadow functions, so we just have to check if the callee's name
       is in the macro table to determine if it is a macro. *)
    
    StringMap.MapsTo x (params, mexpr) M ->
    
    (* There is only one mapping for x in the macro table *)
    (forall params0 mexpr0 params1 mexpr1,
      StringMap.MapsTo x (params0, mexpr0) M ->
      (params0, mexpr0) = (params1, mexpr1) ) ->
    
    (* The macro does not have side-effects *)
    ~ ExprHasSideEffects mexpr ->
    Forall (fun e => ~ ExprHasSideEffects e) es ->
    
    (* Transform macro arguments first *)
    TransformArgs M F es F' es' ->
    
    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname F' ->
    StringMap.Equal F'' (StringMap.add fname (params, Skip, mexpr) F') ->
    
    
    
    
    (* We need to manually add all the premises for function calls that we can't
       intuit from the proof context alone, because macro invocation just doesn't do
       certain things that function calls do, such as evaluating arguments in an
       eager manner *)
    (* These premises are currently too lenient though; we should only use the original
       F in these and prove that they will still hold under F'' *)
       ~ StringMap.In fname M ->
      (* StringMap.MapsTo x (params, fstmt, fexpr) F /\ *) (* We can prove this *)
      (* NoDup params /\ *) (* This is given from the macro invocation *)
      EvalArgs S E G F M es vs S' ->
      StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->
      NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) ->
      NatMapProperties.Disjoint S' Sargs ->
      NatMap.Equal S'' (NatMapProperties.update S' Sargs) ->
      StmtEval S'' Ef G F M Skip S''' ->
      ExprEval S''' Ef G F M mexpr v S'''' ->
      NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
    
    
    TransformExpr M F (CallOrInvocation x es) F'' (CallOrInvocation fname es)
with TransformArgs :
  macro_table -> function_table -> list expr ->
  function_table -> list expr -> Prop :=
  
  (* End of arguments *)
  | TransformArgs_Nil : forall M F es,
    TransformArgs M F nil F es
  
  (* There are arguments left to transform *)
  | TransformArgs_Cons : forall M F e es F' F'' e' es',
    (* Transform the first expression *)
    TransformExpr M F e F' e' ->
    (* Transform the remaining expressions *)
    TransformArgs M F' es F'' es' ->
    TransformArgs M F (e::es) F'' (e'::es')
with TransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=
  
  | Transform_Skip : forall M F,
    TransformStmt M F Skip F Skip.













