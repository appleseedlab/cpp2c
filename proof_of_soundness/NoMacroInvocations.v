(*  NoMacroInvocations.v
    Definitions for relation in which the involved expression
    does not invoke any macros from the given function table, and some
    lemmas related to this relation.
*)

Require Import
  Coq.Lists.List
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  MapLemmas
  NoCallsFromFunctionTable
  SideEffects
  Syntax.

(*  Definition of the relation.
    We need to pass a function table to the relation to check if 
    body of a function contains a macro invocation *)
Inductive ExprNoMacroInvocations : expr -> function_table -> macro_table -> Prop :=
  | NM_Num : forall z F M,
    (*  Numerals cannot invoke macros *)
    ExprNoMacroInvocations (Num z) F M
  | NM_Var : forall x F M,
    (*  Variables cannot invoke macros *)
    ExprNoMacroInvocations (Var x) F M
  | NM_ParenExpr : forall e0 F M,
    (*  The inner expression does not contain an invocation *)
    ExprNoMacroInvocations e0 F M ->
    ExprNoMacroInvocations (ParenExpr e0) F M
  | NM_UnExpr : forall uo e0 F M,
    (*  The inner expression does not contain an invocation *)
    ExprNoMacroInvocations e0 F M ->
    ExprNoMacroInvocations (UnExpr uo e0) F M
  | NM_Bin_Expr : forall bo e1 e2 F M,
    (*  The left operand does not contain an invocation *)
    ExprNoMacroInvocations e1 F M ->
    (*  The right opreand does not contain an invocation *)
    ExprNoMacroInvocations e2 F M ->
    ExprNoMacroInvocations (BinExpr bo e1 e2) F M
  | NM_Assign : forall x e0 F M,
    (*  The inner expression does not contain an invocation *)
    ExprNoMacroInvocations e0 F M ->
    ExprNoMacroInvocations (Assign x e0) F M
  | NM_CallOrInvocation : forall x es F M params fstmt fexpr,
    (*  The invocation is not to a macro *)
    ~ StringMap.In x M ->
    (*  None of the arguments contain an invocation *)
    ExprListNoMacroInvocations es F M ->
    (*  Retrieve the body of the function that is being called *)
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    (*  The statement of the call does not contain a macro invocation *)
    StmtNoMacroInvocations fstmt F M ->
    (*  The return expression of the call does not contain
        any macro invocations *)
    ExprNoMacroInvocations fexpr F M ->
    ExprNoMacroInvocations (CallOrInvocation x es) F M
with ExprListNoMacroInvocations : list expr -> function_table -> macro_table -> Prop :=
  | NM_ExprList_nil : forall F M,
    (*  An empty expression list contains no invocations *)
    ExprListNoMacroInvocations nil F M
  | NM_ExprList_cons : forall e es F M,
    (*  The head of the list does not contain any invocations*)
    ExprNoMacroInvocations e F M ->
    (*  The tail of the list does not contain any invocations *)
    ExprListNoMacroInvocations es F M ->
    ExprListNoMacroInvocations (e::es) F M
with StmtNoMacroInvocations : stmt -> function_table -> macro_table -> Prop :=
| NM_Skip : forall F M,
    (*  Skip statements do no not contain macro invocations *)
    StmtNoMacroInvocations Skip F M
  | NM_Expr : forall e F M,
    (*  The expression does not contain any macro invocations *)
    ExprNoMacroInvocations e F M ->
    StmtNoMacroInvocations (Expr e) F M
  | NM_IfElse : forall cond s1 s2 F M,
    (*  The condition does not contain any macro invocations *)
    ExprNoMacroInvocations cond F M ->
    (*  The true branch does not contain any macro invocations *)
    StmtNoMacroInvocations s1 F M ->
    (*  The false branch does not contain any macro invocations *)
    StmtNoMacroInvocations s2 F M ->
    StmtNoMacroInvocations (IfElse cond s1 s2) F M
  | NM_While : forall cond s0 F M,
    (*  The condition does not contain any macro invocations *)
    ExprNoMacroInvocations cond F M ->
    (*  The while body does not contain any macro invocations *)
    StmtNoMacroInvocations s0 F M ->
    StmtNoMacroInvocations (While cond s0) F M
    (*  An empty compound statement does not contain any macro invocations *)
  | NM_Compound_nil : forall F M,
    StmtNoMacroInvocations (Compound nil) F M
  | NM_Compound_cons : forall s ss F M,
    (*  The first statement does not contain any macro invocations *)
    StmtNoMacroInvocations s F M ->
    (*  The remaining statements do not contain any macro invocations *)
    StmtNoMacroInvocations (Compound ss) F M ->
    StmtNoMacroInvocations (Compound (s::ss)) F M.

(*  Custom induction scheme *)
Scheme ExprNoMacroInvocations_mut := Induction for ExprNoMacroInvocations Sort Prop
with ExprListNoMacroInvocations_mut := Induction for ExprListNoMacroInvocations Sort Prop
with StmtNoMacroInvocations_mut := Induction for StmtNoMacroInvocations Sort Prop.


(*  If an expression does not contain any macro invocations from a given
    macro table, then it does not contain any macro invocations from
    any other macro table equal to the first *)
Lemma M_Equal_ExprNoMacroInvocations : forall e F M_1,
  ExprNoMacroInvocations e F M_1 ->
  forall M_2,
  StringMap.Equal M_1 M_2 ->
  ExprNoMacroInvocations e F M_2.
Proof.
  apply (ExprNoMacroInvocations_mut
    (fun e F M_1 (h : ExprNoMacroInvocations e F M_1) =>
      forall M_2,
      StringMap.Equal M_1 M_2 ->
      ExprNoMacroInvocations e F M_2)
    (fun es F M_1 (h : ExprListNoMacroInvocations es F M_1) =>
      forall M_2,
      StringMap.Equal M_1 M_2 ->
      ExprListNoMacroInvocations es F M_2)
    (fun s F M_1 (h : StmtNoMacroInvocations s F M_1) =>
      forall M_2,
      StringMap.Equal M_1 M_2 ->
      StmtNoMacroInvocations s F M_2)
      ); try constructor; auto.
  - intros. rewrite H2 in n.
    apply NM_CallOrInvocation with params fstmt fexpr; auto.
Qed.


(*  If an expression does not contain any macro invocations from a given
    macro table, and we remove a macro from that table, then the expression
    will not contain any macro invocations under the new table *)
Lemma ExprNoMacroInvocations_remove_ExprNoMacroInvocations : forall e F M,
  ExprNoMacroInvocations e F M ->
  forall x,
  ExprNoMacroInvocations e F (StringMap.remove x M).
Proof.
  apply (ExprNoMacroInvocations_mut
    (fun e F M (h : ExprNoMacroInvocations e F M) =>
      forall x,
      ExprNoMacroInvocations e F (StringMap.remove x M))
    (fun es F M (h : ExprListNoMacroInvocations es F M) =>
      forall x,
      ExprListNoMacroInvocations es F (StringMap.remove x M))
    (fun s F M (h : StmtNoMacroInvocations s F M) =>
      forall x,
      StmtNoMacroInvocations s F (StringMap.remove x M))
      ); try constructor; auto.
  - intros. econstructor; auto.
    + unfold not. intros. apply StringMapFacts.remove_in_iff in H2. destruct H2.
      contradiction.
    + apply m.
Qed.


(*  If an expression terminates under a given context and does not contain
    any macro invocations, then it terminates under a different context
    in which a mapping has been removed from the macro table *)
Lemma EvalExprNoMacroInvocations_remove_EvalExpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  ExprNoMacroInvocations e F M ->
  forall x,
  EvalExpr S E G F (StringMap.remove x M) e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        ExprNoMacroInvocations e F M ->
        forall x,
        EvalExpr S E G F (StringMap.remove x M) e v S')
      (* EvalStmt *)
      (fun S E G F M s S' (h : EvalStmt S E G F M s S' ) =>
        StmtNoMacroInvocations s F M ->
        forall x,
        EvalStmt S E G F (StringMap.remove x M) s S')
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        ExprListNoMacroInvocations es F M ->
        forall x,
        EvalExprList Sprev Ecaller G F (StringMap.remove x M) ps es vs Snext Ef Sargs l ls));
          intros; try (econstructor; solve [eauto]);
          try (inversion_clear H0; solve [econstructor; eauto]);
          try (inversion_clear H1; solve [econstructor; eauto]).
  - (*  Function call *)
    inversion_clear H2.
    assert ( (params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
    inversion H2. subst params0 fstmt0 fexpr0. clear H2.
    apply E_FunctionCall with
    params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + unfold not. intros. apply StringMapFacts.remove_in_iff in H2.
      destruct H2. contradiction.
  - (*  Macro invocation *)
    inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - (*  While *)
    inversion_clear H2. apply E_WhileTrue with v S' S''; auto.
    apply H1. constructor; auto.
Qed.


(*  If an expression list terminates under a given context and does not contain
    any macro invocations, then it terminates under a different context
    in which a mapping has been removed from the macro table *)
Lemma ExprListNoMacroInvocations_remove_EvalExprList : forall Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls,
  EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls->
  ExprListNoMacroInvocations es F M ->
  forall x,
  EvalExprList Sprev Ecaller G F (StringMap.remove x M) ps es vs Snext Ef Sargs l ls.
Proof.
  apply (
    EvalExprList_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        ExprNoMacroInvocations e F M ->
        forall x,
        EvalExpr S E G F (StringMap.remove x M) e v S')
      (* EvalStmt *)
      (fun S E G F M s S' (h : EvalStmt S E G F M s S' ) =>
        StmtNoMacroInvocations s F M ->
        forall x,
        EvalStmt S E G F (StringMap.remove x M) s S')
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        ExprListNoMacroInvocations es F M ->
        forall x,
        EvalExprList Sprev Ecaller G F (StringMap.remove x M) ps es vs Snext Ef Sargs l ls));
          intros; try (econstructor; solve [eauto]);
          try (inversion_clear H0; solve [econstructor; eauto]);
          try (inversion_clear H1; solve [econstructor; eauto]).
  - (*  Function call *)
    inversion_clear H2.
    assert ( (params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
    inversion H2. subst params0 fstmt0 fexpr0. clear H2.
    apply E_FunctionCall with
    params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + unfold not. intros. apply StringMapFacts.remove_in_iff in H2.
      destruct H2. contradiction.
  - (*  Macro invocation *)
    inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - (*  While *)
    inversion_clear H2. apply E_WhileTrue with v S' S''; auto.
    apply H1. constructor; auto.
Qed.

(*  If an expression does not contain any macro invocations from a given
    macro table under a given function table, and we add to that
    function table all the mappings of a function table that the
    expression calls no functions from, then the expression
    will not contain any macro invocations under the new function table *)
Lemma ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations :
  forall e F M,
  ExprNoMacroInvocations e F M ->
  forall F',
  ExprNoCallsFromFunctionTable e F M F' ->
  ExprNoMacroInvocations e (StringMapProperties.update F F') M.
Proof.
  apply (ExprNoMacroInvocations_mut
    (fun e F M (h : ExprNoMacroInvocations e F M) =>
      forall F',
      ExprNoCallsFromFunctionTable e F M F' ->
      ExprNoMacroInvocations e (StringMapProperties.update F F') M)
    (fun es F M (h : ExprListNoMacroInvocations es F M) =>
      forall F',
      ExprListNoCallsFromFunctionTable es F M F' ->
      ExprListNoMacroInvocations es (StringMapProperties.update F F') M)
    (fun s F M (h : StmtNoMacroInvocations s F M) =>
      forall F',
      StmtNoCallsFromFunctionTable s F M F' ->
      StmtNoMacroInvocations s (StringMapProperties.update F F') M)
    ); intros; try (econstructor; solve [eauto]);
        try (inversion_clear H0; solve [econstructor; eauto]);
        try (inversion_clear H1; solve [econstructor; eauto]);
        try (inversion_clear H2; solve [econstructor; eauto]).
  - (*  Function call *)
    inversion_clear H2; auto.
    + assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply NM_CallOrInvocation with params fstmt fexpr; auto.
      apply StringMapProperties.update_mapsto_iff. auto.
    + apply StringMap_mapsto_in in H5. contradiction.
Qed.


(*  If an expression list does not contain any macro invocations from a given
    macro table under a given function table, and we add to that
    function table all the mappings of a function table that the
    expression calls no functions from, then the expression list
    will not contain any macro invocations under the new function table *)
Lemma ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations:
  forall es F M,
  ExprListNoMacroInvocations es F M ->
  forall F',
  ExprListNoCallsFromFunctionTable es F M F' ->
  ExprListNoMacroInvocations es (StringMapProperties.update F F') M.
Proof.
  intros. induction H0.
  - constructor.
  - inversion_clear H.
    constructor; auto.
    apply ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations; auto. 
Qed.


(*  If a statement does not contain any macro invocations from a given
    macro table under a given function table, and we add to that
    function table all the mappings of a function table that the
    expression calls no functions from, then the statement
    will not contain any macro invocations under the new function table *)
Lemma StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations :
  forall s F M,
  StmtNoMacroInvocations s F M ->
  forall F',
  StmtNoCallsFromFunctionTable s F M F' ->
  StmtNoMacroInvocations s (StringMapProperties.update F F') M.
Proof.
  apply (StmtNoMacroInvocations_mut
    (fun e F M (h : ExprNoMacroInvocations e F M) =>
      forall F',
      ExprNoCallsFromFunctionTable e F M F' ->
      ExprNoMacroInvocations e (StringMapProperties.update F F') M)
    (fun es F M (h : ExprListNoMacroInvocations es F M) =>
      forall F',
      ExprListNoCallsFromFunctionTable es F M F' ->
      ExprListNoMacroInvocations es (StringMapProperties.update F F') M)
    (fun s F M (h : StmtNoMacroInvocations s F M) =>
      forall F',
      StmtNoCallsFromFunctionTable s F M F' ->
      StmtNoMacroInvocations s (StringMapProperties.update F F') M)
    ); intros; try (econstructor; solve [eauto]);
        try (inversion_clear H0; solve [econstructor; eauto]);
        try (inversion_clear H1; solve [econstructor; eauto]);
        try (inversion_clear H2; solve [econstructor; eauto]).
  - (*  Function call *)
    inversion_clear H2; auto.
    + assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply NM_CallOrInvocation with params fstmt fexpr; auto.
      apply StringMapProperties.update_mapsto_iff. auto.
    + apply StringMap_mapsto_in in H5. contradiction.
Qed.


(*  If an expression does not contain any macro invocations, and we substitute
    into it a single expression that also does not contain macro invocations,
    then the final expression will also not contain macro invocations *)
Lemma ExprNoMacroInvocations_MSub_ExprNoMacroInvocations : forall mexpr F M,
  ExprNoMacroInvocations mexpr F M ->
  forall e,
  ExprNoMacroInvocations e F M ->
  forall p ef,
  MSub p e mexpr ef ->
  ExprNoMacroInvocations ef F M.
Proof.
  apply (ExprNoMacroInvocations_mut
    (fun mexpr F M (h : ExprNoMacroInvocations mexpr F M) =>
        forall e,
        ExprNoMacroInvocations e F M ->
        forall p ef,
        MSub p e mexpr ef ->
        ExprNoMacroInvocations ef F M)
    (fun es F M (h : ExprListNoMacroInvocations es F M) =>
        forall e,
        ExprNoMacroInvocations e F M ->
        forall p es',
        MSubList p e es es' ->
        ExprListNoMacroInvocations es' F M)
    (fun s F M (h : StmtNoMacroInvocations s F M) =>
      (*  Since macro arguments can't be substituted into statements, we
          assume that no statements contain macro invocations here *)
        StmtNoMacroInvocations s F M ->
        StmtNoMacroInvocations s F M)
        ); intros; try (inversion_clear H0; constructor; auto); auto.
  - inversion H0.
    + subst. auto.
    + subst. constructor.
  - inversion_clear H1. constructor. eapply H. apply H0. apply H2.
  - inversion_clear H1. constructor. eapply H. apply H0. apply H2.
  - inversion_clear H2. constructor.
    + eapply H. apply H1. apply H3.
    + eapply H0. apply H1. apply H4.
  - inversion_clear H1.
    + constructor. apply H with e1 p; auto.
    + constructor. apply H with e1 p; auto.
  - inversion_clear H3. apply NM_CallOrInvocation with params fstmt fexpr; auto.
    apply H with e1 p; auto.
  - inversion_clear H2. constructor.
    + apply H with e2 p; auto.
    + apply H0 with e2 p; auto.
Qed.


(*  If an expression does not contain any macro invocations, and we substitute
    into it a mutiple expressions that also do not contain macro invocations,
    then the final expression will also not contain macro invocations *)
Lemma ExprNoMacroInvocations_NoMacroInvocationExprList_MacroSubst_ExprNoMacroInvocations : forall mexpr F M,
  ExprNoMacroInvocations mexpr F M ->
  forall es,
  ExprListNoMacroInvocations es F M ->
  forall ps ef,
  MacroSubst ps es mexpr ef ->
  ExprNoMacroInvocations ef F M.
Proof.
  intros. induction H1.
  - auto.
  - inversion_clear H0. apply IHMacroSubst; auto.
    + subst. apply ExprNoMacroInvocations_MSub_ExprNoMacroInvocations with mexpr e p; auto.
Qed.


(* If an expression does not have side-effects, then it must not contain a
   macro invocation *)
Lemma not_ExprHasSideEffects_ExprNoMacroInvocations: forall e,
  ~ ExprHasSideEffects e ->
  forall F M,
  ExprNoMacroInvocations e F M.
Proof.
  intros. induction e;
    try (constructor; auto);
    try simpl in *; auto; contradiction.
Qed.
