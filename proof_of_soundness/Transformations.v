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
  
  | Transform_BinExpr : forall M F e1 e2 F1result F2result e1' e2' bo F' F'',
  
    (* Transform the left operand *)
    StringMapProperties.Disjoint F F1result ->
    F' = StringMapProperties.update F F1result ->
    TransformExpr M F e1 F' e1' ->
  
    (* Transform the right operand *)
    StringMapProperties.Disjoint F' F2result ->
    F'' = StringMapProperties.update F' F2result ->
    TransformExpr M F' e2 F'' e2' ->
  
    TransformExpr M F (BinExpr bo e1 e2) F'' (BinExpr bo e1' e2')
  
  | Transform_Assign : forall M F x e F' e',
    TransformExpr M F e F' e' ->
    TransformExpr M F (Assign x e) F' (Assign x e')

  | Transform_FunctionCall :
    forall   F M x es F' F'' F''' F'''' es'
             params fstmt fexpr fstmt' fexpr'
             Fargsresult Fstmtresult Fexprresult fname,
    (* Macros shadow functions, so to determine if what we are calling is a function
       it suffices just to check that its name is not in the macro table and is in
       the function table *)
    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    
    (* Transform function arguments *)
    StringMapProperties.Disjoint F Fargsresult ->
    F' = StringMapProperties.update F Fargsresult ->
    TransformArgs M F es F' es' ->
    
    (* Transform function statement *)
    StringMapProperties.Disjoint F' Fstmtresult ->
    F'' = StringMapProperties.update F' Fstmtresult ->
    TransformStmt M F' fstmt F'' fstmt' ->
    
    (* Transform function return expression *)
    StringMapProperties.Disjoint F'' Fexprresult ->
    F''' = StringMapProperties.update F'' Fexprresult ->
    TransformExpr M F'' fexpr F''' fexpr' ->

    (* Add the transformed function back to the function table under a new name *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F''' ->
    F'''' = StringMap.add fname (params, fstmt', fexpr') F''' ->

    TransformExpr M F (CallOrInvocation x es) F'''' (CallOrInvocation fname es')
    
  | Transform_SideEffectFreeMacro :
    forall  F M x es F' F'' Fes' es' params mexpr fname
            (vs : list Z) (ls : list nat) (v : Z) (Ef : environment)
            (Sargs : store) (S' : store) (S'' : store) (S''' : store)
            (S'''' : store) (S''''' : store),
    (* Again, macros shadow functions, so we just have to check if the callee's name
       is in the macro table to determine if it is a macro. *)
    
    StringMap.MapsTo x (params, mexpr) M ->
    
    (* The macro does not have side-effects *)
    ~ ExprHasSideEffects mexpr ->
    Forall (fun e => ~ ExprHasSideEffects e) es ->
    
    (* Transform macro arguments *)
    StringMapProperties.Disjoint F Fes' ->
    F' = StringMapProperties.update F Fes' ->
    TransformArgs M F es F' es' ->
    
    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F' ->
    F'' = StringMap.add fname (params, Skip, mexpr) F' ->
    
    
    (* We need to manually add all the premises for function calls that we can't
       intuit from the proof context alone, because macro invocation just doesn't do
       certain things that function calls do, such as evaluating arguments in an
       eager manner *)
    
    (* TODO: Fix these premises *)

    (forall (S : store) (E : environment) (G : environment)
            (vs : list Z) (ls : list nat) (v : Z) (Ef : environment)
            (Sargs : store) (S' : store) (S'' : store) (S''' : store)
            (S'''' : store) (S''''' : store),

      EvalArgs S E G F M es vs S' /\
      StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) /\
      NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) /\
      NatMapProperties.Disjoint S' Sargs /\
      NatMap.Equal S'' (NatMapProperties.update S' Sargs) /\
      EvalStmt S'' Ef G F M Skip S''' /\
      
      EvalExpr S''' Ef G F M mexpr v S'''' /\
      NatMap.Equal S''''' (NatMapProperties.restrict S'''' S)) ->
    
    TransformExpr M F (CallOrInvocation x es) F'' (CallOrInvocation fname es')
with TransformArgs :
  macro_table -> function_table -> list expr ->
  function_table -> list expr -> Prop :=
  
  (* End of arguments *)
  | TransformArgs_Nil : forall M F,
    TransformArgs M F nil F nil
  
  (* There are arguments left to transform *)
  | TransformArgs_Cons : forall M F e es F' F'' Fe' Fes' e' es',
    (* Transform the first expression *)
    StringMapProperties.Disjoint F Fe' ->
    F' = StringMapProperties.update F Fe' ->
    TransformExpr M F e F' e' ->
    
    (* Transform the remaining expressions *)
    StringMapProperties.Disjoint F' Fes' ->
    F'' = StringMapProperties.update F' Fes' ->
    TransformArgs M F' es F'' es' ->
    
    
    TransformArgs M F (e::es) F'' (e'::es')
with TransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=
  
  | Transform_Skip : forall M F,
    TransformStmt M F Skip F Skip.



Inductive StepTransformExpr :
  macro_table -> function_table -> expr ->
  function_table -> expr -> Prop :=
  
  | StepTransform_Var : forall M F x,
    StepTransformExpr M F (Var x) F (Var x)
  
  | StepTransform_ParenExpr : forall M F e0 F' e0',
    StepTransformExpr M F e0 F' e0' ->
    StepTransformExpr M F (ParenExpr e0) F' (ParenExpr e0')
  
  | StepTransform_UnExpr : forall M F e0 F' e0' uo,
    StepTransformExpr M F e0 F' e0' ->
    StepTransformExpr M F (UnExpr uo e0) F' (UnExpr uo e0')
  
  
  | StepTransform_BinExprConst : forall M F bo z1 z2,
    StepTransformExpr M F (BinExpr bo (Num z1) (Num z2)) F (BinExpr bo (Num z1) (Num z2))
  | StepTransform_BinExpr1 : forall M F bo e1 e2 e1' F',
    StepTransformExpr M F e1 F' e1' ->
    StepTransformExpr M F (BinExpr bo e1 e2) F' (BinExpr bo e1' e2)
  | StepTransform_BinExpr2 : forall M F bo z1 e2 e2' F',
    StepTransformExpr M F e2 F' e2' ->
    StepTransformExpr M F (BinExpr bo (Num z1) e2) F' (BinExpr bo (Num z1) e2')
  
  | StepTransform_Assign : forall M F x e0 F' e0',
    StepTransformExpr M F e0 F' e0' ->
    StepTransformExpr M F (Assign x e0) F' (Assign x e0')
  
  | StepTransform_Call : forall M F x es F' es',
    StepTransformArgs M F es F' es' ->
    StepTransformExpr M F (CallOrInvocation x es) F (CallOrInvocation x es')
  
with StepTransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=
  
  | StepTransformSkip : forall M F,
    StepTransformStmt M F Skip F Skip
  
with StepTransformArgs :
  macro_table -> function_table -> list expr ->
  function_table -> list expr -> Prop :=
  | StepTransformArgsNil : forall M F,
    StepTransformArgs M F nil F nil
  | StepTransformArgsCons : forall M F e es F' F'' e' es',
    StepTransformExpr M F e F' e' ->
    StepTransformArgs M F' es F'' es' ->
    StepTransformArgs M F (e::es) F'' (e'::es').


Scheme StepTransformExpr_mut := Induction for StepTransformExpr Sort Prop
with StepTransformArgs_mut := Induction for StepTransformArgs Sort Prop.


Lemma StepTransformExpr_StepExpr_StepExpr : forall M F e0 F' e1,
  StepTransformExpr M F e0 F' e1 ->
  forall S E G e' S',
    StepExpr S E G F M e0 e' S' ->
    StepExpr S E G F' M e1 e' S'.
Proof.

  intros.
  apply (
    StepTransformExpr_mut
      (fun M F e0 F' e1 (h : StepTransformExpr M F e0 F' e1) =>
        forall S E G e' S',
          StepExpr S E G F M e0 e' S' ->
          StepExpr S E G F M e1 e' S')
      (fun M F es F' es' (h : StepTransformArgs M F es F' es') =>
        forall S E G F M S' fexpr fexpr' ps,
          StepArgs S E G F M fexpr ps es fexpr' S' ->
          StepArgs S E G F M fexpr ps es' fexpr' S')
    ) with e0 F; auto.
  - intros. inversion H2; subst.
    + inversion s.
    + apply Step_ParenExpr1. apply H1. auto.
  - intros. inversion H2; subst.
    + inversion s; subst.
    + constructor. apply H1. auto.
  - intros. inversion H2; subst.
    + inversion s; subst.
    + apply Step_BinExpr1; auto.
    + inversion s.
  - intros. inversion H2; subst.
    + inversion s.
    + inversion H13.
    + apply Step_BinExpr2. apply H1. auto.
  - intros. inversion H2; subst.
    + inversion s.
    + inversion s.
    + apply Step_Assign1. apply H1. auto.
  - intros. inversion H2; subst.
    apply Step_FunctionCall with params fstmt fexpr; auto.
  - intros. admit.
  - admit.
  - admit.
Abort.





