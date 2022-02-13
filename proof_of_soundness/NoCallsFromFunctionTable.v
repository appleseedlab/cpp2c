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
  SideEffects
  Syntax
  MapLemmas.


(*  Relation only holds if an expression does not contain any calls from the
    given function table F' *)
Inductive ExprNoCallsFromFunctionTable :
  expr -> function_table -> macro_table -> function_table -> Prop :=
  | NC_Num : forall z F M F',
    (*  Numerals of course do not call functions *)
    ExprNoCallsFromFunctionTable (Num z) F M F'
  | NC_Var : forall x F M F',
    (*  Variables of course do not call functions *)
    ExprNoCallsFromFunctionTable (Var x) F M F'
  | NC_ParenExpr : forall e0 F M F',
    (*  The inner expression does not call a function in the function table *)
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (ParenExpr e0) F M F'
  | NC_UnExpr : forall uo e0 F M F',
    (*  The inner expression does not call a function in the function table *)
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (UnExpr uo e0) F M F'
  | NC_BinExpr : forall bo e1 e2 F M F',
    (*  The left operand does not call a function in the function table *)
    ExprNoCallsFromFunctionTable e1 F M F' ->
    (*  The right operand does not call a function in the function table *)
    ExprNoCallsFromFunctionTable e2 F M F' ->
    ExprNoCallsFromFunctionTable (BinExpr bo e1 e2) F M F'
  | NC_Assign : forall x e0 F M F',
    (*  The inner expression does not call a function in the function table *)
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (Assign x e0) F M F'
  | NC_FunctionCall: forall x es F M F' params fstmt fexpr,
    (*  Verify that we have found a function *)
    ~ StringMap.In x M ->
    (*  Verify that the function name is not present in the table *)
    ~ StringMap.In x F' ->
    (*  None of the arguments contain a call to a function from the function
        table *)
    ExprListNoCallsFromFunctionTable es F M F' ->
    (*  Retreive the function's body *)
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    (*  The function statement does not contain a call to a function from
        the function table *)
    StmtNoCallsFromFunctionTable fstmt F M F' ->
    (*  The function expression does not contain a call to a function from
        the function table *)
    ExprNoCallsFromFunctionTable fexpr F M F' ->
    ExprNoCallsFromFunctionTable (CallOrInvocation x es) F M F'
  | NC_MacroInvocation: forall x es F M F' params mexpr ef,
    (*  Verify that the macro name is not present in the table *)
    ~ StringMap.In x F' ->
    (*  None of the arguments contain a call to a function from the function
        table *)
    ExprListNoCallsFromFunctionTable es F M F' ->
    (*  Retrieve the macro definition *)
    StringMap.MapsTo x (params, mexpr) M ->
    (*  The function body does not contain a call to a function from
        the function table *)
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
    (*  An empty list does not contain any function calls *)
    ExprListNoCallsFromFunctionTable nil F M F'
  | NC_ExprList_cons : forall e es F M F',
    (*  The head of the list does not contain a call to a function from the
        function table *)
    ExprNoCallsFromFunctionTable e F M F' ->
    (*  The tail of the list does not contain a call to a function from the
        function table *)
    ExprListNoCallsFromFunctionTable es F M F' ->
    ExprListNoCallsFromFunctionTable (e::es) F M F'
with StmtNoCallsFromFunctionTable :
  stmt -> function_table -> macro_table -> function_table -> Prop :=
  | NC_Skip : forall F M F',
    (*  Skip statements do not call any functions *)
    StmtNoCallsFromFunctionTable Skip F M F'
  | NC_Expr : forall e F M F',
    (*  The expression does not contain any function calls *)
    ExprNoCallsFromFunctionTable e F M F' ->
    StmtNoCallsFromFunctionTable (Expr e) F M F'
  | NC_IfElse : forall cond s1 s2 F M F',
    (*  The condition does not contain any function calls *)
    ExprNoCallsFromFunctionTable cond F M F' ->
    (*  The true branch does not contain any function calls *)
    StmtNoCallsFromFunctionTable s1 F M F' ->
    (*  The false branch does not contain any function calls *)
    StmtNoCallsFromFunctionTable s2 F M F' ->
    StmtNoCallsFromFunctionTable (IfElse cond s1 s2) F M F'
  | NC_While : forall cond s0 F M F',
    (*  The condition does not contain any function calls *)
    ExprNoCallsFromFunctionTable cond F M F' ->
    (*  The while body does not contain any function calls *)
    StmtNoCallsFromFunctionTable s0 F M F' ->
    StmtNoCallsFromFunctionTable (While cond s0) F M F'
    (*  An empty compound statement does not contain any function calls *)
  | NC_Compound_nil : forall F M F',
    StmtNoCallsFromFunctionTable (Compound nil) F M F'
  | NC_Compound_cons : forall s ss F M F',
    (*  The first statement does not contain any function calls *)
    StmtNoCallsFromFunctionTable s F M F' ->
    (*  The remaining statements do not contain any function calls *)
    StmtNoCallsFromFunctionTable (Compound ss) F M F' ->
    StmtNoCallsFromFunctionTable (Compound (s::ss)) F M F'.


(*  Simple way of saying that an expression does not call a specific
    function *)
Definition ExprFunctionNotCalled
  (e : expr) (F : function_table)
  (M : macro_table) (x: string) (fdef : function_definition) : Prop :=
  ExprNoCallsFromFunctionTable e F M
    (StringMap.add x fdef (StringMap.empty function_definition)).


(*  Simple way of saying that an expression list does not call a specific
    function *)
Definition ExprListFunctionNotCalled
  (es : list expr) (F : function_table)
  (M : macro_table) (x: string) (fdef : function_definition) : Prop :=
  ExprListNoCallsFromFunctionTable es F M
    (StringMap.add x fdef (StringMap.empty function_definition)).


(*  Simple way of saying that a statement does not call a specific
    function *)
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

(*  Custom induction scheme *)
Scheme ExprNoCallsFromFunctionTable_mut := Induction for ExprNoCallsFromFunctionTable Sort Prop
with ExprListNoCallsFromFunctionTable_mut := Induction for ExprListNoCallsFromFunctionTable Sort Prop
with StmtNoCallsFromFunctionTable_mut := Induction for StmtNoCallsFromFunctionTable Sort Prop.


(*  If an expression contains no call to a function table, and the expression
    terminates under some context in which a function table it may
    contain calls from is updated with the function table it does not contain
    calls from, then it will terminate under the context in which its
    function table that it may contain calls from has not been updated with
    the table that it does not contain calls from *)
Lemma EvalExpr_update_F_ExprNoCallsFromFunctionTable_EvalExpr : forall S E G F'' M e v S',
  EvalExpr S E G F'' M e v S' ->
  forall F F',
  ExprNoCallsFromFunctionTable e F M F' ->
  F'' = StringMapProperties.update F F' ->
  EvalExpr S E G F M e v S'.
Proof.
  apply (EvalExpr_mut
      (*  EvalExpr *)
      (fun S E G F'' M e v S' (h : EvalExpr S E G F'' M e v S') =>
        forall F F',
        ExprNoCallsFromFunctionTable e F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExpr S E G F M e v S')
      (*  EvalStmt *)
      (fun S E G F'' M s S' (h : EvalStmt S E G F'' M s S') =>
        forall F F',
        StmtNoCallsFromFunctionTable s F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalStmt S E G F M s S')
      (*  EvalExprList *)
      (fun Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls) =>
        forall F F',
        ExprListNoCallsFromFunctionTable es F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls)
    ); intros; auto;
      try (econstructor; solve [eauto]);
      try (inversion_clear H0; econstructor; solve [eauto]);
      try (inversion_clear H1; econstructor; solve [eauto]).
  - (*  Function call*)
    inversion_clear H2.
    + assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. subst F.
        apply StringMapProperties.update_mapsto_iff. right. auto. }
        inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply E_FunctionCall with
        params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs ; auto.
      * apply H with F'; auto.
      * apply H0 with F'; auto.
      * apply H1 with F'; auto.
    + apply StringMap_mapsto_in in H6. contradiction.
  - (*  Macro invocation*)
    inversion_clear H0.
    + apply StringMap_mapsto_in in m. contradiction.
    + assert ((params, mexpr) = (params0, mexpr0)).
      { apply StringMapFacts.MapsTo_fun with M x; auto. }
      inversion H0; subst params0 mexpr0; clear H0.
      assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
      subst ef0.
      apply E_MacroInvocation with params mexpr M' ef; subst; auto.
      apply H with F'; auto.
  - (*  While *)
    inversion H2. subst. econstructor 6; eauto.
Qed.


(*  If an expression contains no call to a function table, and the expression
    terminates under some context, then it will terminate under the context in
    which its function table that it may contain calls from has been updated
    with the table that it does not contain calls from *)
Lemma EvalExpr_ExprNoCallsFromFunctionTable_update_F_EvalExpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  forall F' F'',
  ExprNoCallsFromFunctionTable e F M F' ->
  F'' = StringMapProperties.update F F' ->
  EvalExpr S E G F'' M e v S'.
Proof.
  apply (EvalExpr_mut
      (*  EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        forall F' F'',
        ExprNoCallsFromFunctionTable e F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExpr S E G F'' M e v S')
      (*  EvalStmt *)
      (fun S E G F M s S' (h : EvalStmt S E G F M s S') =>
        forall F' F'',
        StmtNoCallsFromFunctionTable s F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalStmt S E G F'' M s S')
      (*  EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall F' F'',
        ExprListNoCallsFromFunctionTable es F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls)
    ); intros; auto;
      try (econstructor; solve [eauto]);
      try (inversion_clear H0; econstructor; solve [eauto]);
      try (inversion_clear H1; econstructor; solve [eauto]).
  - (*  Function call *)
    inversion_clear H2.
    + assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply E_FunctionCall with
        params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs ; auto.
      * rewrite H3. apply StringMapProperties.update_mapsto_iff.
          right. auto.
      * apply H with F'; auto.
      * apply H0 with F'; auto.
      * apply H1 with F'; auto.
    + apply StringMap_mapsto_in in H6. contradiction.
  - (*  Macro invocation *)
    inversion_clear H0.
    + apply StringMap_mapsto_in in m. contradiction.
    + assert ((params, mexpr) = (params0, mexpr0)).
      { apply StringMapFacts.MapsTo_fun with M x; auto. }
      inversion H0; subst params0 mexpr0; clear H0.
      assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
      subst ef0.
      apply E_MacroInvocation with params mexpr M' ef; subst; auto.
      apply H with F'; auto.
  - (*  While *)
    inversion H2. subst. econstructor 6; eauto.
Qed.

(*  Same as EvalExpr_update_F_ExprNoCallsFromFunctionTable_EvalExpr,
    but for expression lists *)
Lemma EvalExprList_update_F_ExprListNoCallsFromFunctionTable_EvalExprList : forall Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls,
  EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls ->
  forall F F',
  ExprListNoCallsFromFunctionTable es F M F' ->
  F'' = StringMapProperties.update F F' ->
  EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls.
Proof.
  apply (EvalExprList_mut
      (*  EvalExpr *)
      (fun S E G F'' M e v S' (h : EvalExpr S E G F'' M e v S') =>
        forall F F',
        ExprNoCallsFromFunctionTable e F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExpr S E G F M e v S')
      (*  EvalStmt *)
      (fun S E G F'' M s S' (h : EvalStmt S E G F'' M s S') =>
        forall F F',
        StmtNoCallsFromFunctionTable s F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalStmt S E G F M s S')
      (*  EvalExprList *)
      (fun Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls) =>
        forall F F',
        ExprListNoCallsFromFunctionTable es F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls)
    ); intros; auto;
      try (econstructor; solve [eauto]);
      try (inversion_clear H0; econstructor; solve [eauto]);
      try (inversion_clear H1; econstructor; solve [eauto]).
  - (*  Function call*)
    inversion_clear H2.
    + assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. subst F.
        apply StringMapProperties.update_mapsto_iff. right. auto. }
        inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply E_FunctionCall with
        params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs ; auto.
      * apply H with F'; auto.
      * apply H0 with F'; auto.
      * apply H1 with F'; auto.
    + apply StringMap_mapsto_in in H6. contradiction.
  - (*  Macro invocation*)
    inversion_clear H0.
    + apply StringMap_mapsto_in in m. contradiction.
    + assert ((params, mexpr) = (params0, mexpr0)).
      { apply StringMapFacts.MapsTo_fun with M x; auto. }
      inversion H0; subst params0 mexpr0; clear H0.
      assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
      subst ef0.
      apply E_MacroInvocation with params mexpr M' ef; subst; auto.
      apply H with F'; auto.
  - (*  While *)
    inversion H2. subst. econstructor 6; eauto.
Qed.

(*  Same as EvalExpr_ExprNoCallsFromFunctionTable_update_F_EvalExpr,
    but for expression lists *)
Lemma EvalExprList_ExprNoCallsFromFunctionTable_update_F_EvalExprList : forall Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls,
  EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls ->
  forall F' F'',
  ExprListNoCallsFromFunctionTable es F M F' ->
  F'' = StringMapProperties.update F F' ->
  EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls.
Proof.
  apply (EvalExprList_mut
      (*  EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        forall F' F'',
        ExprNoCallsFromFunctionTable e F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExpr S E G F'' M e v S')
      (*  EvalStmt *)
      (fun S E G F M s S' (h : EvalStmt S E G F M s S') =>
        forall F' F'',
        StmtNoCallsFromFunctionTable s F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalStmt S E G F'' M s S')
      (*  EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall F' F'',
        ExprListNoCallsFromFunctionTable es F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls)
    ); intros; auto;
      try (econstructor; solve [eauto]);
      try (inversion_clear H0; econstructor; solve [eauto]);
      try (inversion_clear H1; econstructor; solve [eauto]).
  - (*  Function call *)
    inversion_clear H2.
    + assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply E_FunctionCall with
        params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs ; auto.
      * rewrite H3. apply StringMapProperties.update_mapsto_iff.
          right. auto.
      * apply H with F'; auto.
      * apply H0 with F'; auto.
      * apply H1 with F'; auto.
    + apply StringMap_mapsto_in in H6. contradiction.
  - (*  Macro invocation *)
    inversion_clear H0.
    + apply StringMap_mapsto_in in m. contradiction.
    + assert ((params, mexpr) = (params0, mexpr0)).
      { apply StringMapFacts.MapsTo_fun with M x; auto. }
      inversion H0; subst params0 mexpr0; clear H0.
      assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
      subst ef0.
      apply E_MacroInvocation with params mexpr M' ef; subst; auto.
      apply H with F'; auto.
  - (*  While *)
    inversion H2. subst. econstructor 6; eauto.
Qed.

(*  Same as EvalExpr_update_F_ExprNoCallsFromFunctionTable_EvalExpr,
    but for statements *)
Lemma EvalStmt_update_F_StmtNoCallsFromFunctionTable_EvalStmt : forall S E G F'' M s S',
  EvalStmt S E G F'' M s S' ->
  forall F F',
  StmtNoCallsFromFunctionTable s F M F' ->
  F'' = StringMapProperties.update F F' ->
  EvalStmt S E G F M s S'.
Proof.
  apply (EvalStmt_mut
      (*  EvalExpr *)
      (fun S E G F'' M e v S' (h : EvalExpr S E G F'' M e v S') =>
        forall F F',
        ExprNoCallsFromFunctionTable e F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExpr S E G F M e v S')
      (*  EvalStmt *)
      (fun S E G F'' M s S' (h : EvalStmt S E G F'' M s S') =>
        forall F F',
        StmtNoCallsFromFunctionTable s F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalStmt S E G F M s S')
      (*  EvalExprList *)
      (fun Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls) =>
        forall F F',
        ExprListNoCallsFromFunctionTable es F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls)
    ); intros; auto;
      try (econstructor; solve [eauto]);
      try (inversion_clear H0; econstructor; solve [eauto]);
      try (inversion_clear H1; econstructor; solve [eauto]).
  - (*  Function call*)
    inversion_clear H2.
    + assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. subst F.
        apply StringMapProperties.update_mapsto_iff. right. auto. }
        inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply E_FunctionCall with
        params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs ; auto.
      * apply H with F'; auto.
      * apply H0 with F'; auto.
      * apply H1 with F'; auto.
    + apply StringMap_mapsto_in in H6. contradiction.
  - (*  Macro invocation*)
    inversion_clear H0.
    + apply StringMap_mapsto_in in m. contradiction.
    + assert ((params, mexpr) = (params0, mexpr0)).
      { apply StringMapFacts.MapsTo_fun with M x; auto. }
      inversion H0; subst params0 mexpr0; clear H0.
      assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
      subst ef0.
      apply E_MacroInvocation with params mexpr M' ef; subst; auto.
      apply H with F'; auto.
  - (*  While *)
    inversion H2. subst. econstructor 6; eauto.
Qed.

(*  Same as EvalExpr_ExprNoCallsFromFunctionTable_update_F_EvalExpr,
    but for statements *)
Lemma EvalStmt_StmtNoCallsFromFunctionTable_update_F_EvalStmt: forall S E G F M s S',
  EvalStmt S E G F M s S' ->
  forall F' F'',
  StmtNoCallsFromFunctionTable s F M F' ->
  F'' = StringMapProperties.update F F' ->
  EvalStmt S E G F'' M s S'.
Proof.
  apply (EvalStmt_mut
      (*  EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        forall F' F'',
        ExprNoCallsFromFunctionTable e F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExpr S E G F'' M e v S')
      (*  EvalStmt *)
      (fun S E G F M s S' (h : EvalStmt S E G F M s S') =>
        forall F' F'',
        StmtNoCallsFromFunctionTable s F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalStmt S E G F'' M s S')
      (*  EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall F' F'',
        ExprListNoCallsFromFunctionTable es F M F' ->
        F'' = StringMapProperties.update F F' ->
        EvalExprList Sprev Ecaller G F'' M ps es vs Snext Ef Sargs l ls)
    ); intros; auto;
      try (econstructor; solve [eauto]);
      try (inversion_clear H0; econstructor; solve [eauto]);
      try (inversion_clear H1; econstructor; solve [eauto]).
  - (*  Function call *)
    inversion_clear H2.
    + assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      apply E_FunctionCall with
        params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs ; auto.
      * rewrite H3. apply StringMapProperties.update_mapsto_iff.
          right. auto.
      * apply H with F'; auto.
      * apply H0 with F'; auto.
      * apply H1 with F'; auto.
    + apply StringMap_mapsto_in in H6. contradiction.
  - (*  Macro invocation *)
    inversion_clear H0.
    + apply StringMap_mapsto_in in m. contradiction.
    + assert ((params, mexpr) = (params0, mexpr0)).
      { apply StringMapFacts.MapsTo_fun with M x; auto. }
      inversion H0; subst params0 mexpr0; clear H0.
      assert (ef = ef0). { apply MacroSubst_deterministic with params es mexpr; auto. }
      subst ef0.
      apply E_MacroInvocation with params mexpr M' ef; subst; auto.
      apply H with F'; auto.
  - (*  While *)
    inversion H2. subst. econstructor 6; eauto.
Qed.


(* If an expression does not have side-effects, then it must not contain a
   call from a function table *)
Lemma not_ExprHasSideEffects_ExprNoCallsFromFunctionTable : forall e,
  ~ ExprHasSideEffects e ->
  forall F M F',
  ExprNoCallsFromFunctionTable e F M F'.
Proof.
  intros. induction e;
    try constructor; auto;
    try (simpl in *; auto; contradiction).
Qed.
