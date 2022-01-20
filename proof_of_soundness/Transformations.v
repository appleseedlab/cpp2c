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
  
  | Transform_BinExpr : forall M F e1 e2 F' F'' F''' e1' e2' bo,
    TransformExpr M F e1 F' e1' ->
    TransformExpr M F e2 F'' e2' ->
    
    (* Note that we don't explicity create F''' here. In the implementation, F''' will
       be created as the the unification of F' and F''. *)
    (* We need these extra theorems until we resolve the unique names problem, but
       these should make sense for now*)
    (* If we can evaluate the left expression under its F transformation, then we can
       evaluate it under the unified F list *)
    (forall S E G v S',
      ExprEval S E G F' M e1' v S' -> ExprEval S E G F''' M e1' v S') ->
    (* Similarly, if we can evaluate the right expression under its F transformation,
       then we can evaluate it under the unified F list as well *)
    (forall S'0 E G v2 S',
      ExprEval S'0 E G F'' M e2' v2 S' -> ExprEval S'0 E G F''' M e2' v2 S') ->
    TransformExpr M F (BinExpr bo e1 e2) F''' (BinExpr bo e1' e2')
    
    | Transform_Assign : forall M F x e F' e',
      TransformExpr M F e F' e' ->
      TransformExpr M F (Assign x e) F' (Assign x e')

    | Transform_FunctionCall : forall F M x es,
      (* Macros shadow functions, so to determine if what we are calling is a function
         it suffices just to check that its name is not in the macro table and is in
         the function table *)
      ~ StringMap.In x M ->
      StringMap.In x F ->
      (* TODO: Transform function arguments *)
      TransformExpr M F (CallOrInvocation x es) F (CallOrInvocation x es)
      
    | Transform_SideEffectFreeMacro :
      forall  F M x es F' params mexpr fname
              (vs : list Z) (ls : list nat) (Ef : environment)
              (Sargs : store) (S'' : store) (S''' : store) (S'''' : store)
              (S''''' : store),
      (* Again, macros shadow functions, so we just have to check if the callee's name
         is in the macro table to determine if it is a macro. *)
      
      StringMap.In x M ->
      
      (* Assert that there is only one mapping for x in the macro table *)
      (forall params' mexpr',
        StringMap.MapsTo x (params', mexpr') M -> params' = params /\ mexpr' = mexpr) ->
      
      (* The macro does not have side-effects *)
      ~ ExprHasSideEffects mexpr ->
      Forall (fun e => ~ ExprHasSideEffects e) es ->
      
      (* The name for transformed macro function is not already present in the function
         table *)
      ~ StringMap.In fname F ->
      StringMap.Equal F' (StringMap.add fname (params, Skip, mexpr) F) ->
      
      
      (* TODO: Transform macro arguments *)
      
      
      (* We need to manually add all the premises for function calls that we can't
         intuit from the proof context alone, because macro invocation just doesn't do
         certain things that function calls do, such as evaluating arguments in an
         eager manner *)
       ~ StringMap.In fname M ->
      (* StringMap.MapsTo x (params, fstmt, fexpr) F /\ *) (* We can prove this *)
      (* NoDup params /\ *) (* This is given from the macro invocation *)
      (forall (S : store) (E : environment) (G : environment)
              (vs : list Z) (ls : list nat) (v : Z) (Ef : environment)
              Sargs S' S'' S''' S'''' S''''',
      EvalArgs S E G F' M es vs S' /\
      StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) /\
      NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) /\
      NatMapProperties.Disjoint S' Sargs /\
      NatMap.Equal S'' (NatMapProperties.update S' Sargs) /\
      StmtEval S'' Ef G F' M Skip S''' /\
      (* Not sure if this is too generous a premise? *)
      ExprEval S''' Ef G F' M mexpr v S'''' /\
      (* Only keep in the store the L-value mappings that were there when
         the function was called; i.e., remove from the store all mappings
         whose L-value is in Ef/Sargs. *)
      NatMap.Equal S''''' (NatMapProperties.restrict S'''' S)) ->
      
      
      TransformExpr M F (CallOrInvocation x es) F' (CallOrInvocation fname es).

