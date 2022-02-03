Require Import
  Coq.Strings.String.

From Cpp2C Require Import
  ConfigVars
  EvalRules
  MapTheorems
  NoCallsFromFunctionTable
  Syntax.


Inductive ExprNoMacroInvocations : expr -> function_table -> macro_table -> Prop :=
  | NM_Num : forall z F M,
    ExprNoMacroInvocations (Num z) F M
  | NM_Var : forall x F M,
    ExprNoMacroInvocations (Var x) F M
  | NM_ParenExpr : forall e0 F M,
    ExprNoMacroInvocations e0 F M ->
    ExprNoMacroInvocations (ParenExpr e0) F M
  | NM_UnExpr : forall uo e0 F M,
    ExprNoMacroInvocations e0 F M ->
    ExprNoMacroInvocations (UnExpr uo e0) F M
  | NM_Bin_Expr : forall bo e1 e2 F M,
    ExprNoMacroInvocations e1 F M ->
    ExprNoMacroInvocations e2 F M ->
    ExprNoMacroInvocations (BinExpr bo e1 e2) F M
  | NM_Assign : forall x e0 F M,
    ExprNoMacroInvocations e0 F M ->
    ExprNoMacroInvocations (Assign x e0) F M
  | NM_CallOrInvocation : forall x es F M params fstmt fexpr,
    ~ StringMap.In x M ->
    NoMacroInvocationsArgs es F M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    ExprNoMacroInvocations fexpr F M ->
    ExprNoMacroInvocations (CallOrInvocation x es) F M
with NoMacroInvocationsArgs : list expr -> function_table -> macro_table -> Prop :=
  | NM_Args_nil : forall F M,
    NoMacroInvocationsArgs nil F M
  | NM_Args_cons : forall e es F M,
    ExprNoMacroInvocations e F M ->
    NoMacroInvocationsArgs es F M ->
    NoMacroInvocationsArgs (e::es) F M.


Scheme ExprNoMacroInvocations_mut := Induction for ExprNoMacroInvocations Sort Prop
with NoMacroInvocationsArgs_mut := Induction for NoMacroInvocationsArgs Sort Prop.


Lemma ExprNoMacroInvocations_remove_ExprNoMacroInvocations : forall e F M,
  ExprNoMacroInvocations e F M ->
  forall x,
  ExprNoMacroInvocations e F (StringMap.remove x M).
Proof.
  apply (ExprNoMacroInvocations_mut
    (fun e F M (h : ExprNoMacroInvocations e F M) =>
      forall x,
      ExprNoMacroInvocations e F (StringMap.remove x M))
    (fun es F M (h : NoMacroInvocationsArgs es F M) =>
      forall x,
      NoMacroInvocationsArgs es F (StringMap.remove x M))); try constructor; auto.
  - intros. econstructor; auto.
    + unfold not. intros. apply StringMapFacts.remove_in_iff in H1. destruct H1.
      contradiction.
    + apply m.
Qed.


Lemma ExprNoMacroInvocations_remove_EvalExpr : forall S E G F M e v S',
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
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall (x : string),
        EvalStmt S E G F (StringMap.remove x M) stmt S' (* TODO: Fix once more statement are added *))
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        NoMacroInvocationsArgs es F M ->
        forall x,
        EvalArgs Sprev Ecaller G F (StringMap.remove x M) ps es vs Snext Ef Sargs l )); auto; intros; try constructor.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - inversion_clear H0; auto.
  - inversion_clear H0; auto.
  - inversion_clear H1. econstructor. auto. auto.
  - inversion_clear H0. apply E_Assign_Local with l S'; auto.
  - inversion_clear H0. apply E_Assign_Global with l S'; auto.
  - inversion_clear H2. apply E_FunctionCall with
    params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + unfold not. intros. apply StringMapFacts.remove_in_iff in H2.
      destruct H2. contradiction.
    + apply H1; auto.
      assert ( (params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion_clear H2. auto.
  - inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - inversion_clear H1. econstructor; auto.
Qed.


Lemma ExprNoMacroInvocations_remove_EvalArgs : forall Sprev Ecaller G F M ps es vs Snext Ef Sargs l,
  EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l ->
  NoMacroInvocationsArgs es F M ->
  forall x,
  EvalArgs Sprev Ecaller G F (StringMap.remove x M) ps es vs Snext Ef Sargs l.
Proof.
  apply (
    EvalArgs_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        ExprNoMacroInvocations e F M ->
        forall x,
        EvalExpr S E G F (StringMap.remove x M) e v S')
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall (x : string),
        EvalStmt S E G F (StringMap.remove x M) stmt S' (* TODO: Fix once more statement are added *))
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        NoMacroInvocationsArgs es F M ->
        forall x,
        EvalArgs Sprev Ecaller G F (StringMap.remove x M) ps es vs Snext Ef Sargs l )); auto; intros; try constructor.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - inversion_clear H0; auto.
  - inversion_clear H0; auto.
  - inversion_clear H1. econstructor. auto. auto.
  - inversion_clear H0. apply E_Assign_Local with l S'; auto.
  - inversion_clear H0. apply E_Assign_Global with l S'; auto.
  - inversion_clear H2. apply E_FunctionCall with
    params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + unfold not. intros. apply StringMapFacts.remove_in_iff in H2.
      destruct H2. contradiction.
    + apply H1; auto.
      assert ( (params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion_clear H2. auto.
  - inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
  - inversion_clear H1. econstructor; auto.
Qed.


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
    (fun es F M (h : NoMacroInvocationsArgs es F M) =>
      forall F',
      ExprNoCallsFromFunctionTableArgs es F M F' ->
      NoMacroInvocationsArgs es (StringMapProperties.update F F') M)); intros; try constructor; auto.
  - inversion_clear H0; auto.
  - inversion_clear H0; auto.
  - inversion_clear H1; auto.
  - inversion_clear H1; auto.
  - inversion_clear H0; auto.
  - inversion_clear H1; auto.
    + assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion H1; subst params0 fstmt0 fexpr0; clear H1.
      apply NM_CallOrInvocation with params fstmt fexpr; auto.
      apply StringMapProperties.update_mapsto_iff. auto.
    + apply StringMap_mapsto_in in H4. contradiction.
  - inversion_clear H1; auto.
  - inversion_clear H1; auto.
Qed.


Lemma ExprNoMacroInvocations_msub_ExprNoMacroInvocations : forall mexpr F M,
  ExprNoMacroInvocations mexpr F M ->
  forall e,
  ExprNoMacroInvocations e F M ->
  forall p,
  ExprNoMacroInvocations (msub p e mexpr) F M.
Proof.
  intros.
  induction H; simpl.
  - constructor.
  - destruct ((p =? x)%string); auto; constructor.
  - constructor. auto.
  - constructor. auto.
  - constructor. auto. auto.
  - destruct ( (p =? x)%string ).
    + destruct e; constructor; apply IHExprNoMacroInvocations; auto.
    + constructor. apply IHExprNoMacroInvocations; auto.
  - apply NM_CallOrInvocation with params fstmt fexpr; auto.
Qed.


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
    (fun es F M (h : NoMacroInvocationsArgs es F M) =>
        forall e,
        ExprNoMacroInvocations e F M ->
        forall p es',
        MSubList p e es es' ->
        NoMacroInvocationsArgs es' F M)); intros; try (inversion_clear H0; constructor; auto).
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
  - inversion_clear H2. apply NM_CallOrInvocation with params fstmt fexpr; auto.
    apply H with e0 p; auto.
  - inversion_clear H2. constructor.
    + apply H with e1 p; auto.
    + apply H0 with e1 p; auto.
Qed.


Lemma ExprNoMacroInvocations_NoMacroInvocationArgs_MacroSubst_ExprNoMacroInvocations : forall mexpr F M,
  ExprNoMacroInvocations mexpr F M ->
  forall es,
  NoMacroInvocationsArgs es F M ->
  forall ps ef,
  MacroSubst ps es mexpr ef ->
  ExprNoMacroInvocations ef F M.
Proof.
  intros. induction H1.
  - auto.
  - inversion_clear H0. apply IHMacroSubst; auto.
    + subst. apply ExprNoMacroInvocations_MSub_ExprNoMacroInvocations with mexpr e p; auto.
Qed.