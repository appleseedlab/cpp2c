Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  Syntax
  MapTheorems.


(* Relation only holds if an expression does not contain any calls from the given
   function table F' *)
Inductive ExprNoCallsFromFunctionTable :
  expr -> function_table -> macro_table -> function_table -> Prop :=
  | NC_Num : forall z F M F',
    ExprNoCallsFromFunctionTable (Num z) F M F'
  | NC_Var : forall x F M F',
    ExprNoCallsFromFunctionTable (Var x) F M F'
  | NC_ParenExpr : forall e0 F M F',
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (ParenExpr e0) F M F'
  | NC_UnExpr : forall uo e0 F M F',
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (UnExpr uo e0) F M F'
  | NC_BinExpr : forall bo e1 e2 F M F',
    ExprNoCallsFromFunctionTable e1 F M F' ->
    ExprNoCallsFromFunctionTable e2 F M F' ->
    ExprNoCallsFromFunctionTable (BinExpr bo e1 e2) F M F'
  | NC_Assign : forall x e0 F M F',
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (Assign x e0) F M F'
  | NC_FunctionCall: forall x es F M F' params fstmt fexpr,
    ~ StringMap.In x M ->
    ~ StringMap.In x F' ->
    ExprListNoCallsFromFunctionTable es F M F' ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    StmtNoCallsFromFunctionTable fstmt F M F' ->
    ExprNoCallsFromFunctionTable fexpr F M F' ->
    ExprNoCallsFromFunctionTable (CallOrInvocation x es) F M F'
  | NC_MacroInvocation: forall x es F M F' params mexpr ef,
    ~ StringMap.In x F' ->
    ExprListNoCallsFromFunctionTable es F M F' ->
    StringMap.MapsTo x (params, mexpr) M ->
    ExprNoCallsFromFunctionTable mexpr F M F' ->
    MacroSubst params es mexpr ef ->
    (* We use (StringMap.remove x M) here because after removing the
       originally called macro from the macro table (to prevent recursively
       expanding the macro) we might expose a function from the function table
       that the macro was shadowing.
       E.g., say we are checking for a call to the function f in this code:

         #DEFINE f()  f()
         int f(void) { return 0; }

         int main(void) { return f(); }

       In this case, f is in both the function and macro table.
       If we searched the original macro table after expanding the
       macro f for the function f, then we would not find it, because
       the macro f would still be there shadowing it.
       In the actual code fragment though, we ultimately would
       call the function f after expanding the macro f, because the
       CPP would expand the macro once, not recursively expand it, 
       and expose the function f to the program. *)
    ExprNoCallsFromFunctionTable ef F (StringMap.remove x M) F' ->
    ExprNoCallsFromFunctionTable (CallOrInvocation x es) F M F'
with ExprListNoCallsFromFunctionTable :
  list expr -> function_table -> macro_table -> function_table -> Prop :=
  | NC_ExprList_nil : forall F M F',
    ExprListNoCallsFromFunctionTable nil F M F'
  | NC_ExprList_cons : forall e es F M F',
    ExprNoCallsFromFunctionTable e F M F' ->
    ExprListNoCallsFromFunctionTable es F M F' ->
    ExprListNoCallsFromFunctionTable (e::es) F M F'
with StmtNoCallsFromFunctionTable :
  stmt -> function_table -> macro_table -> function_table -> Prop :=
  | NC_Skip : forall F M F',
    StmtNoCallsFromFunctionTable Skip F M F'.


Definition ExprFunctionNotCalled
  (e : expr) (F : function_table)
  (M : macro_table) (x: string) (fdef : function_definition) : Prop :=
  ExprNoCallsFromFunctionTable e F M
    (StringMap.add x fdef (StringMap.empty function_definition)).


Definition ExprListFunctionNotCalled
  (es : list expr) (F : function_table)
  (M : macro_table) (x: string) (fdef : function_definition) : Prop :=
  ExprListNoCallsFromFunctionTable es F M
    (StringMap.add x fdef (StringMap.empty function_definition)).


Definition StmtFunctionNotCalled
  (st : stmt) (F : function_table)
  (M : macro_table) (x: string) (fdef : function_definition) : Prop :=
  StmtNoCallsFromFunctionTable st F M
    (StringMap.add x fdef (StringMap.empty function_definition)).


Lemma ExprNoCallsFromFunctionTable_remove_macro_ExprNoCallsFromFunctionTable :
  forall e F M F',
  ExprNoCallsFromFunctionTable e F M F' ->
  forall x,
  ExprNoCallsFromFunctionTable e F (StringMap.remove x M) F'.
Proof.
  intros e F m F' H. induction H; intros; try constructor; auto.
  - apply NC_FunctionCall with params fstmt fexpr; auto.
    + rewrite StringMapFacts.remove_in_iff.
      (* Issue: Removing a macro from the macro table might expose a function that
         it shadowed *)
Abort.


Scheme ExprNoCallsFromFunctionTable_mut := Induction for ExprNoCallsFromFunctionTable Sort Prop
with ExprListNoCallsFromFunctionTable_mut := Induction for ExprListNoCallsFromFunctionTable Sort Prop
with StmtNoCallsFromFunctionTable_mut := Induction for StmtNoCallsFromFunctionTable Sort Prop.


Lemma EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr : forall e F M F',
  ExprNoCallsFromFunctionTable e F M F' ->
  forall S E G v S',
  EvalExpr S E G (StringMapProperties.update F F') M e v S' <->
  EvalExpr S E G F M e v S'.
Proof.
  split.
  - revert e F M F' H S E G v S'.
    apply (ExprNoCallsFromFunctionTable_mut
      (fun e F M F' (h : ExprNoCallsFromFunctionTable e F M F') =>
        forall S E G v S',
        EvalExpr S E G (StringMapProperties.update F F') M e v S' ->
        EvalExpr S E G F M e v S')
      (fun es F M F' (h : ExprListNoCallsFromFunctionTable es F M F') =>
        forall S E G params vs S' Ef Sargs l ls,
        EvalExprList S E G (StringMapProperties.update F F') M params es vs S' Ef Sargs l ls ->
        EvalExprList S E G F M params es vs S' Ef Sargs l ls)
      (fun stmt F M F' (h : StmtNoCallsFromFunctionTable stmt F M F') =>
        forall S E G S',
        EvalStmt S E G (StringMapProperties.update F F') M stmt S' ->
        EvalStmt S E G F M stmt S')
      ); intros; try constructor; auto.
    +
      inversion_clear H. constructor.
    +
      inversion_clear H.
      * econstructor; eauto.
      * apply E_GlobalVar with l; auto.
    +
      inversion_clear H0; auto.
    +
      inversion_clear H0; constructor; auto.
    +
      inversion_clear H1. apply E_BinExpr with S'0; auto.
    +
      inversion_clear H0.
      *
        apply E_Assign_Local with l S'0; auto.
      *
        apply E_Assign_Global with l S'0; auto.
    +
      inversion_clear H2.
      *
        assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
        { apply StringMapFacts.MapsTo_fun with F x; auto.
          apply StringMapProperties.update_mapsto_iff in H4. destruct H4.
          + apply StringMap_mapsto_in in H2. contradiction.
          + apply H2.
        } inversion H2; subst params0 fstmt0 fexpr0; clear H2.
        apply E_FunctionCall with
          params fstmt fexpr l ls Ef Sargs S'0 S'' S''' S'''' vs ; auto.
      *
        apply StringMap_mapsto_in in H3. contradiction.
    +
      inversion_clear H2.
      *
        apply StringMap_mapsto_in in m. contradiction.
      *
        assert ((params, mexpr) = (params0, mexpr0)).
        { apply StringMapFacts.MapsTo_fun with M x; auto. }
        inversion H2; subst params0 mexpr0; clear H2.
        assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
        subst ef0.
        apply E_MacroInvocation with params mexpr M' ef; subst; auto.
    +
      inversion_clear H. constructor.
    +
      inversion_clear H1. apply EvalExprList_cons with Snext; auto.
    +
      inversion_clear H. constructor.
  -
    revert e F M F' H S E G v S'.
    apply (ExprNoCallsFromFunctionTable_mut
    (fun e F M F' (h : ExprNoCallsFromFunctionTable e F M F') =>
      forall S E G v S',
      EvalExpr S E G F M e v S' ->
      EvalExpr S E G (StringMapProperties.update F F') M e v S')
    (fun es F M F' (h : ExprListNoCallsFromFunctionTable es F M F') =>
      forall S E G params vs S' Ef Sargs l ls,
      EvalExprList S E G F M params es vs S' Ef Sargs l ls ->
      EvalExprList S E G (StringMapProperties.update F F') M params es vs S' Ef Sargs l ls)
    (fun stmt F M F' (h : StmtNoCallsFromFunctionTable stmt F M F') =>
      forall S E G S',
      EvalStmt S E G F M stmt S' ->
      EvalStmt S E G (StringMapProperties.update F F') M stmt S')
    ); intros; try constructor; auto.
    +
      inversion_clear H. constructor.
    +
      inversion_clear H.
      * econstructor; eauto.
      * apply E_GlobalVar with l; auto.
    +
      inversion_clear H0; auto.
    +
      inversion_clear H0; constructor; auto.
    +
      inversion_clear H1. apply E_BinExpr with S'0; auto.
    +
      inversion_clear H0.
      *
        apply E_Assign_Local with l S'0; auto.
      *
        apply E_Assign_Global with l S'0; auto.
    +
      inversion_clear H2.
      *
        assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
        { apply StringMapFacts.MapsTo_fun with F x; auto. }
        inversion H2; subst params0 fstmt0 fexpr0; clear H2.
        apply E_FunctionCall with
          params fstmt fexpr l ls Ef Sargs S'0 S'' S''' S'''' vs; auto.
        apply StringMapProperties.update_mapsto_iff. right. auto.
      *
        apply StringMap_mapsto_in in H3. contradiction.
    +
      inversion_clear H2.
      *
        apply StringMap_mapsto_in in m. contradiction.
      *
        assert ((params, mexpr) = (params0, mexpr0)).
        { apply StringMapFacts.MapsTo_fun with M x; auto. }
        inversion H2; subst params0 mexpr0; clear H2.
        assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
        subst ef0.
        apply E_MacroInvocation with params mexpr M' ef; subst; auto.
    + inversion_clear H. constructor.
    + inversion_clear H1. apply EvalExprList_cons with Snext; auto.
    + inversion_clear H. constructor.
Qed.


Lemma EvalExprListNoCallsFromFunctionTable_update_EvalExprListNoCallsFromFunctionTable: forall es F M F',
  ExprListNoCallsFromFunctionTable es F M F' ->
  forall S E G params vs S' Ef Sargs l ls,
  EvalExprList S E G (StringMapProperties.update F F') M params es vs S' Ef Sargs l ls <->
  EvalExprList S E G F M params es vs S' Ef Sargs l ls.
Proof.
  intros es F M F' H.
  remember (StringMapProperties.update F F'). split.
  -
    intros. induction H0.
    +
      constructor.
    +
      subst F0. inversion_clear H. 
      apply EvalExprList_cons with Snext; auto.
      apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr with F';
        auto.
  - intros. induction H0.
    +
      constructor.
    +
      subst t. inversion_clear H.
      apply EvalExprList_cons with Snext; auto.
      apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr; auto.
Qed.


Lemma EvalStmtNoCallsFromFunctionTable_update_EvalStmtNoCallsFromFunctionTable: forall stmt F M F',
  StmtNoCallsFromFunctionTable stmt F M F' ->
  forall S E G S',
  EvalStmt S E G (StringMapProperties.update F F') M stmt S' <->
  EvalStmt S E G F M stmt S'.
Proof.
  intros es F M F' H.
  remember (StringMapProperties.update F F'). split.
  -
    intros. induction H0.
    + constructor.
  -
    intros. induction H0.
    + constructor.
Qed.
