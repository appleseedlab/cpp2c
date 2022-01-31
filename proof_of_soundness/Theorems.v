Require Import
  Coq.FSets.FMapList
  Coq.Logic.Classical_Prop
  Coq.Lists.List
  Coq.Strings.String
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  MapTheorems
  EvalRules
  Transformations.


Lemma no_side_effects_no_store_change : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  NatMap.Equal S S'.
Proof.
  intros e H S E G F M v S' E1.
  induction E1.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHE1. apply H.
  - apply IHE1. apply H.
  - unfold ExprHasSideEffects in H. fold ExprHasSideEffects in H.
    apply Classical_Prop.not_or_and in H.
    rewrite <- IHE1_1 in IHE1_2.
    apply IHE1_2.  apply H. apply H.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Lemma no_side_effects_no_store_change_eq : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  S = S'.
Proof.
  intros e H S E G F M v S' E1.
  induction E1.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHE1. apply H.
  - apply IHE1. apply H.
  - unfold ExprHasSideEffects in H. fold ExprHasSideEffects in H.
    apply Classical_Prop.not_or_and in H.
    rewrite <- IHE1_1 in IHE1_2.
    apply IHE1_2.  apply H. apply H.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Lemma no_side_effects_evalexpr_evalexpr : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  EvalExpr S E G F M e v S' ->
  EvalExpr S E G F M e v S.
Proof.
  intros e H S E G F M v S' E1.
  induction E1.
  - apply E_Num.
  - apply E_LocalVar with l; assumption.
  - apply E_GlobalVar with l; assumption.
  - apply E_ParenExpr. apply IHE1. assumption.
  - apply E_UnExpr. apply IHE1. assumption.
  - unfold ExprHasSideEffects in H. fold ExprHasSideEffects in H.
    apply Classical_Prop.not_or_and in H. destruct H. apply E_BinExpr with S'.
    + assumption.
    + apply no_side_effects_no_store_change_eq in E1_1.
      * subst. apply IHE1_2. assumption.
      * assumption.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Theorem no_side_effects_no_store_change_evalargs : forall S E G F M ps es S' vs Ef Sargs l,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  NatMap.Equal S S'.
Proof.
  intros. induction H0.
  - reflexivity.
  - inversion H. apply no_side_effects_no_store_change in H0.
    rewrite H0. apply IHEvalArgs. assumption. assumption.
Qed.


Theorem no_side_effects_no_store_change_evalargs_eq : forall S E G F M ps es S' vs Ef Sargs l,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  S = S'.
Proof.
  intros. induction H0.
  - reflexivity.
  - inversion H. apply no_side_effects_no_store_change_eq in H0.
    rewrite H0. apply IHEvalArgs. assumption. assumption.
Qed.


Lemma no_side_effects_evalargs_evalargs: forall S E G F M ps es S' vs Ef Sargs l,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  EvalArgs S E G F M ps es vs S Ef Sargs l.
Proof.
  intros. induction H0.
  - apply EvalArgs_nil.
  - inversion H; subst. apply EvalArgs_cons with Snext; auto.
    + apply no_side_effects_no_store_change_eq in H0; subst; auto.
Qed.


Lemma skip_no_side_effects : forall S E G F M S',
  EvalStmt S E G F M Skip S' ->
  NatMap.Equal S S'.
Proof.
  intros. induction H. reflexivity.
Qed.


Lemma skip_no_side_effects_eq : forall S E G F M S',
  EvalStmt S E G F M Skip S' ->
  S = S'.
Proof.
  intros. induction H. reflexivity.
Qed.


(* The following lemmas involve all parts of program evaluation
   (e.g., expression, argument list, and statement evaluation).
   Coq's built-in induction tactic is not powerful enough to provide
   us with the induction hypotheses necessary to prove these lemmas, so
   we must define our own induction schema for these proofs *)
Scheme EvalExpr_mut := Induction for EvalExpr Sort Prop
with EvalStmt_mut := Induction for EvalStmt Sort Prop
with EvalArgs_mut := Induction for EvalArgs Sort Prop.


Lemma evalstmt_notin_F_add_evalstmt : forall S E G F M stmt S',
  EvalStmt S E G F M stmt S' ->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalStmt S E G (StringMap.add x fdef F) M stmt S'.
Proof.
(*
  This proof could be solved instead with the following ltac code:
    intros. induction H; try constructor.
  Instead I have opted to use our custom schema here so that it may serve
  as a simple demonstration of how to use schemas *)
  intros. apply (
    (* First we apply the appropriate schema like a tactic *)
    EvalStmt_mut
      (* Then we have to define a custom inductive hypothesis for each Prop
         that the one we are inducting over is mutually inductive with
         (in this case just the EvalStmt Prop since statement evaluation
         currently only includes skip statements, which don't
         involve expressions) *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S') =>
        EvalStmt S E G (StringMap.add x fdef F) M stmt S')
  ); try constructor; auto.
Qed.


Lemma evalstmt_disjoint_update_F_evalstmt : forall S E G F M stmt S',
  EvalStmt S E G F M stmt S' ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalStmt S E G (StringMapProperties.update F F') M stmt S'.
Proof.
  intros. induction H; try constructor. Qed.


Lemma evalexpr_notin_F_add_evalexpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalExpr S E G (StringMap.add x fdef F) M e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalExpr S E G (StringMap.add x fdef F) M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalStmt S E G (StringMap.add x fdef F) M stmt S' )
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalArgs Sprev Ecaller G (StringMap.add x fdef F) M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma evalexpr_disjoint_update_F_evalexpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalExpr S E G (StringMapProperties.update F F') M e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExpr S E G (StringMapProperties.update F F') M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalStmt S E G (StringMapProperties.update F F') M stmt S' )
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.update F F') M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + apply StringMapProperties.update_mapsto_iff. right. split.
      * auto.
      * apply StringMap_mapsto_in in m.
        unfold StringMapProperties.Disjoint in H2.
        assert (~ (StringMap.In (elt:=function_definition) x F /\
                    StringMap.In (elt:=function_definition) x F')).
        { apply H2. }
        apply Classical_Prop.not_and_or in H3. destruct H3.
        -- contradiction.
        -- auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma evalexpr_disjoint_diff_F_evalexpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalExpr S E G (StringMapProperties.diff F F') M e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExpr S E G (StringMapProperties.diff F F') M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalStmt S E G (StringMapProperties.diff F F') M stmt S' )
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.diff F F') M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + apply StringMapProperties.diff_mapsto_iff. split.
      * auto.
      * apply StringMap_mapsto_in in m.
        unfold StringMapProperties.Disjoint in H2.
        assert (~ (StringMap.In (elt:=function_definition) x F /\
                    StringMap.In (elt:=function_definition) x F')).
        { apply H2. }
        apply Classical_Prop.not_and_or in H3. destruct H3.
        -- contradiction.
        -- auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma evalargs_notin_F_add_evalargs : forall S E G F M ps es vs S' Ef Sargs l,
  EvalArgs S E G F M ps es vs S' Ef Sargs l->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalArgs S E G (StringMap.add x fdef F) M ps es vs S' Ef Sargs l.
Proof.
  apply (
    EvalArgs_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalExpr S E G (StringMap.add x fdef F) M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalStmt S E G (StringMap.add x fdef F) M stmt S' )
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalArgs Sprev Ecaller G (StringMap.add x fdef F) M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma evalargs_disjoint_update_F_evalargs : forall S E G F M ps es vs S' Ef Sargs l,
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalArgs S E G (StringMapProperties.update F F') M ps es vs S' Ef Sargs l.
Proof.
  apply (
    EvalArgs_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExpr S E G (StringMapProperties.update F F') M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalStmt S E G (StringMapProperties.update F F') M stmt S' )
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l
      (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.update F F') M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + apply StringMapProperties.update_mapsto_iff. right. split.
      * auto.
      * apply StringMap_mapsto_in in m.
        unfold StringMapProperties.Disjoint in H2.
        assert (~ (StringMap.In (elt:=function_definition) x F /\
                    StringMap.In (elt:=function_definition) x F')).
        { apply H2. }
        apply Classical_Prop.not_and_or in H3. destruct H3.
        -- contradiction.
        -- auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma no_side_effects_msub_no_side_effects : forall mexpr p e,
  ~ ExprHasSideEffects mexpr ->
  ~ ExprHasSideEffects e ->
  ~ ExprHasSideEffects (msub p e mexpr).
Proof.
  induction mexpr; auto.
  - (* Var *)
    intros. simpl in *. destruct ((p =? x)%string); auto.
  - (* BinExpr *)
    intros. simpl in *. apply Classical_Prop.not_or_and in H. destruct H.
    apply Classical_Prop.and_not_or. split; auto.
  - (* Assign *)
    intros. simpl in *. contradiction.
Qed.


Lemma no_side_effects_Msub_no_side_effects : forall p e mexpr ef,
  ~ ExprHasSideEffects mexpr ->
  ~ ExprHasSideEffects e ->
    MSub p e mexpr ef ->
  ~ ExprHasSideEffects ef.
Proof.
  intros. induction H1; auto.
  simpl in *. apply Classical_Prop.not_or_and in H. destruct H.
  apply Classical_Prop.and_not_or. auto.
Qed.


Theorem no_side_effects_macrosubst_no_side_effects : forall mexpr params es ef,
  ~ ExprHasSideEffects mexpr ->
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  MacroSubst params es mexpr ef ->
  ~ ExprHasSideEffects ef.
Proof.
  intros.
  induction H1; auto.
  inversion H0; subst.
  apply IHMacroSubst; eauto using no_side_effects_Msub_no_side_effects.
Qed.


(* This proof is easy right now because we only have Skip statements *)
Lemma mapsto_transformstmt_mapsto : forall x fdef F M stmt F' stmt', 
  StringMap.MapsTo x fdef F ->
  TransformStmt M F stmt F' stmt' ->
  StringMap.MapsTo x fdef F'.
Proof.
  intros. induction H0. assumption.
Qed.


Lemma no_side_effects_expr_transform_no_side_effects : forall e,
  ~ ExprHasSideEffects e ->
  forall M F F' e',
    TransformExpr M F e F' e' ->
    ~ ExprHasSideEffects e'.
Proof.
  intros. induction H0; auto.
  -
    simpl in H. apply Classical_Prop.not_or_and in H. destruct H.
    unfold ExprHasSideEffects. fold ExprHasSideEffects.
    apply Classical_Prop.and_not_or. split; auto.
Qed.


Lemma no_side_effects_Forall_no_side_effects : forall es,
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  forall M F F' es',
    TransformArgs M F es F' es' ->
  Forall (fun e => ~ ExprHasSideEffects e) es'.
Proof.
  intros. induction H0.
  - auto.
  - inversion H. subst. apply Forall_cons.
    * apply no_side_effects_expr_transform_no_side_effects with e M F F'; auto.
    * apply IHTransformArgs; auto.
Qed.


(* This proof is easy right now because we only have Skip statements *)
Lemma evalstmt_transformargs_evalstmt : forall S E G F M stmt S' F' stmt',
  EvalStmt S E G F M stmt S' ->
  TransformStmt M F stmt F' stmt' ->
  EvalStmt S E G F' M stmt S'.
Proof.
  intros. induction H0. assumption.
Qed.


Lemma evalexpr_var_x_in_E_or_G : forall S E G F M x v S',
  EvalExpr S E G F M (Var x) v S' ->
  StringMap.In x E \/ StringMap.In x G.
Proof.
  intros. inversion_clear H.
  - left. apply StringMap_mapsto_in in H0. auto.
  - right. apply StringMap_mapsto_in in H1. auto.
Qed.


Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformArgs_mut := Induction for TransformArgs Sort Prop
with TransformStmt_mut := Induction for TransformStmt Sort Prop.


Scheme NoMacroInvocations_mut := Induction for NoMacroInvocations Sort Prop
with NoMacroInvocationsArgs_mut := Induction for NoMacroInvocationsArgs Sort Prop.


Lemma nomacroinvocations_remove_nomacroinvocations : forall e F M,
  NoMacroInvocations e F M ->
  forall x,
  NoMacroInvocations e F (StringMap.remove x M).
Proof.
  apply (NoMacroInvocations_mut
    (fun e F M (h : NoMacroInvocations e F M) =>
      forall x,
      NoMacroInvocations e F (StringMap.remove x M))
    (fun es F M (h : NoMacroInvocationsArgs es F M) =>
      forall x,
      NoMacroInvocationsArgs es F (StringMap.remove x M))); try constructor; auto.
  - intros. econstructor; auto.
    + unfold not. intros. apply StringMapFacts.remove_in_iff in H1. destruct H1.
      contradiction.
    + apply m.
Qed.


Lemma nomacroinvocations_remove_evalexpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  NoMacroInvocations e F M ->
  forall x,
  EvalExpr S E G F (StringMap.remove x M) e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        NoMacroInvocations e F M ->
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


Lemma nomacroinvocations_remove_evalargs : forall Sprev Ecaller G F M ps es vs Snext Ef Sargs l,
  EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l ->
  NoMacroInvocationsArgs es F M ->
  forall x,
  EvalArgs Sprev Ecaller G F (StringMap.remove x M) ps es vs Snext Ef Sargs l.
Proof.
  apply (
    EvalArgs_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S') =>
        NoMacroInvocations e F M ->
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


Lemma nomacroinvocations_transformexpr_no_change : forall e F M,
  NoMacroInvocations e F M ->
  forall F' e',
  TransformExpr M F e F' e' ->
  e = e'.
Proof.
  apply (NoMacroInvocations_mut
    (fun e F M (h : NoMacroInvocations e F M) =>
      forall F' e',
        TransformExpr M F e F' e' ->
        e = e')
    (fun es F M (h : NoMacroInvocationsArgs es F M) =>
      forall F' es',
        TransformArgs M F es F' es' ->
        es = es')).
  - intros. inversion_clear H; auto.
  - intros. inversion_clear H; auto.
  - intros. inversion_clear H0.
    assert (e0 = e0'). { apply H with F'; auto. }
    subst. auto.
  - intros. inversion_clear H0.
    assert (e0 = e0'). { apply H with F'; auto. }
    subst. auto.
  - intros. inversion_clear H1.
    assert (e1 = e1'). { apply H with F'; auto. }
    assert (e2 = e2'). { apply H0 with F'; auto. }
    subst. auto.
  - intros. inversion_clear H0.
    assert (e0 = e'0). { apply H with F'; auto. }
    subst; auto.
  - intros. inversion_clear H1.
    + assert (es = es'). { apply H with F'; auto. }
      subst; auto.
    + apply StringMap_mapsto_in in H2. contradiction.
  - intros. inversion_clear H. auto.
  - intros. inversion_clear H1.
    assert (e = e'). { apply H with F'; auto. }
    assert (es = es'0). { apply H0 with F'; auto. }
    subst; auto.
Qed.


Lemma nomacroinvocations_transformexpr_nomacroinvocations :
  forall M F e F' e',
  TransformExpr M F e F' e' ->
  NoMacroInvocations e F M ->
  NoMacroInvocations e' F' M.
Proof.
  apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
      NoMacroInvocations e F M ->
      NoMacroInvocations e' F' M)
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
      NoMacroInvocationsArgs es F M ->
      NoMacroInvocationsArgs es' F' M)
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
      True (* TODO: Fix this later once we add more statements *))); auto.
  - intros. inversion_clear H0. constructor; auto.
  - intros. inversion_clear H0. constructor; auto.
  - intros. inversion_clear H1. constructor; auto.
  - intros. inversion_clear H0. constructor; auto.
  - intros. inversion_clear H2. econstructor; auto.
    + rewrite e. apply StringMapFacts.add_mapsto_iff. left; auto.
    + apply H1.
      assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion_clear H2. auto.
  - intros. inversion_clear H1. apply StringMap_mapsto_in in m. contradiction.
  - intros. inversion_clear H1. constructor; auto.
Qed.



Lemma nomacroinvocations_transformargs_nomacroinvocations : forall M F es F' es',
  TransformArgs M F es F' es' ->
  NoMacroInvocationsArgs es F M ->
  NoMacroInvocationsArgs es' F' M.
Proof.
  apply (TransformArgs_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
      NoMacroInvocations e F M ->
      NoMacroInvocations e' F' M)
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
      NoMacroInvocationsArgs es F M ->
      NoMacroInvocationsArgs es' F' M)
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
      True (* TODO: Fix this later once we add more statements *))); auto.
  - intros. inversion_clear H0. constructor; auto.
  - intros. inversion_clear H0. constructor; auto.
  - intros. inversion_clear H1. constructor; auto.
  - intros. inversion_clear H0. constructor; auto.
  - intros. inversion_clear H2. econstructor; auto.
    + rewrite e. apply StringMapFacts.add_mapsto_iff. left; auto.
    + apply H1.
      assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
      { apply StringMapFacts.MapsTo_fun with F x; auto. }
      inversion_clear H2. auto.
  - intros. inversion_clear H1. apply StringMap_mapsto_in in m. contradiction.
  - intros. inversion_clear H1. constructor; auto.
Qed.


Lemma nomacroinvocationsargs_transformargs_no_change : forall es F M,
  NoMacroInvocationsArgs es F M ->
  forall F' es',
  TransformArgs M F es F' es' ->
  es = es'.
Proof.
  intros. induction H0; auto.
  inversion_clear H.
  assert (e=e').
  { apply nomacroinvocations_transformexpr_no_change with F M F'; auto. }
  assert (es=es'). { apply IHTransformArgs; auto. }
  subst; auto.
Qed.


Lemma nomacroinvocations_msub_nomacroinvocations : forall mexpr F M,
  NoMacroInvocations mexpr F M ->
  forall e,
  NoMacroInvocations e F M ->
  forall p,
  NoMacroInvocations (msub p e mexpr) F M.
Proof.
  intros.
  induction H; simpl.
  - constructor.
  - destruct ((p =? x)%string); auto; constructor.
  - constructor. auto.
  - constructor. auto.
  - constructor. auto. auto.
  - destruct ( (p =? x)%string ).
    + destruct e; constructor; apply IHNoMacroInvocations; auto.
    + constructor. apply IHNoMacroInvocations; auto.
  - apply NM_CallOrInvocation with params fstmt fexpr; auto.
Qed.


Lemma nomacroinvocations_Msub_nomacroinvocations : forall mexpr F M,
  NoMacroInvocations mexpr F M ->
  forall e,
  NoMacroInvocations e F M ->
  forall p ef,
  MSub p e mexpr ef ->
  NoMacroInvocations ef F M.
Proof.
  apply (NoMacroInvocations_mut
    (fun mexpr F M (h : NoMacroInvocations mexpr F M) =>
        forall e,
        NoMacroInvocations e F M ->
        forall p ef,
        MSub p e mexpr ef ->
        NoMacroInvocations ef F M)
    (fun es F M (h : NoMacroInvocationsArgs es F M) =>
        forall e,
        NoMacroInvocations e F M ->
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
    + constructor. apply H with e p; auto.
    + constructor. apply H with e p; auto.
  - inversion_clear H2. apply NM_CallOrInvocation with params fstmt fexpr; auto.
    apply H with e p; auto.
  - inversion_clear H2. constructor.
    + apply H with e0 p; auto.
    + apply H0 with e0 p; auto.
Qed.


Lemma nomacroinvocations_msubst_nomacroinvocations : forall mexpr F M,
  NoMacroInvocations mexpr F M ->
  forall es,
  NoMacroInvocationsArgs es F M ->
  forall ps ef,
  MacroSubst ps es mexpr ef ->
  NoMacroInvocations ef F M.
Proof.
  intros. induction H1.
  - auto.
  - inversion_clear H0. apply IHMacroSubst; auto.
    + subst. apply nomacroinvocations_Msub_nomacroinvocations with mexpr e p; auto.
Qed.


Lemma novarsinenvironment_msub_novarsinenvironment : forall mexpr E,
  NoVarsInEnvironment mexpr E ->
  forall e,
  NoVarsInEnvironment e E ->
  forall p,
  NoVarsInEnvironment (msub p e mexpr) E.
Proof.
  intros.
  induction H; try constructor; try (fold msub; apply IHNoVarsInEnvironment; auto).
  - simpl. destruct ((p =? x)%string); auto. constructor. auto.
  - fold msub. apply IHNoVarsInEnvironment1; auto.
  - fold msub. apply IHNoVarsInEnvironment2; auto.
  - simpl. destruct ( (p =? x)%string); auto.
    + destruct e; constructor; auto.
      inversion_clear H0; auto.
    + constructor; auto.
  - auto.
  - apply H1.
Qed.


Scheme NoVarsInEnvironment_mut := Induction for NoVarsInEnvironment Sort Prop
with NoVarsInEnvironmentArgs_mut := Induction for NoVarsInEnvironmentArgs Sort Prop.


(* TODO *)
Lemma novarsinenvironment_Msub_novarsinenvironment : forall mexpr E,
  NoVarsInEnvironment mexpr E ->
  forall e,
  NoVarsInEnvironment e E ->
  forall p ef,
  MSub p e mexpr ef ->
  NoVarsInEnvironment ef E.
Proof.
  apply (NoVarsInEnvironment_mut
    (fun mexpr E (h : NoVarsInEnvironment mexpr E) =>
      forall e,
      NoVarsInEnvironment e E ->
      forall p ef,
      MSub p e mexpr ef ->
      NoVarsInEnvironment ef E)
    (fun es E (h : NoVarsInEnvironmentArgs es E) =>
      forall e,
      NoVarsInEnvironment e E ->
      forall p es',
      MSubList p e es es' ->
      NoVarsInEnvironmentArgs es' E)); intros; try constructor; auto.
  - inversion_clear H0; constructor.
  - inversion H0.
    + subst; auto.
    + subst. constructor; auto.
  - inversion_clear H1. constructor. eapply H; eauto.
  - inversion_clear H1. constructor. eapply H; eauto.
  - inversion_clear H2. constructor.
    + eapply H; eauto.
    + eapply H0; eauto.
  - inversion H1. 
    + subst. constructor. inversion H0; auto. eapply H; eauto.
    + subst. constructor; auto. eapply H; eauto.
  - inversion_clear H1. constructor; eauto.
  - inversion_clear H0. constructor.
  - inversion_clear H2. constructor.
    + eapply H; eauto.
    + eapply H0; eauto.
Qed.


Lemma novarsinenvironment_msubst_novarsinenvironment : forall mexpr E,
  NoVarsInEnvironment mexpr E ->
  forall es,
  Forall (fun e => NoVarsInEnvironment e E) es ->
  forall ps ef,
  MacroSubst ps es mexpr ef ->
  NoVarsInEnvironment ef E.
Proof.
  intros. induction H1.
  - auto.
  - inversion_clear H0. apply IHMacroSubst; auto.
    apply novarsinenvironment_Msub_novarsinenvironment with mexpr e p; auto.
Qed.


Lemma no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil :
  forall mexpr,
  (* The macro body must not have side-effects *)
  ~ ExprHasSideEffects mexpr ->
  forall F M,
  (* The macro must not contain a macro invocation *)
  NoMacroInvocations mexpr F M->
  forall Ecaller,
  (* The macro body must not rely on variables from the caller's scope.
     Global variables, however, are allowed. *)
  NoVarsInEnvironment mexpr Ecaller ->
  forall ef,
  MacroSubst nil nil mexpr ef ->
  forall S G v S''',
  EvalExpr S Ecaller G F M ef v S''' ->
  forall S' Ef Sargs l,
  EvalArgs S Ecaller G F M nil nil nil S' Ef Sargs l ->
  (* We will prove that S = S' since there are no side-effects.
     S' and Sargs must be distinct so that we don't overwrite pre-existing
     L-values *)
  NatMapProperties.Disjoint S' Sargs ->
  forall v0 S'''0,
  EvalExpr (NatMapProperties.update S' Sargs) Ef G F M mexpr v0 S'''0 ->
  v = v0.
Proof.
  intros.
  assert ((NatMapProperties.update S' Sargs) = S'''0).
  { apply no_side_effects_no_store_change_eq in H6; auto. }
  rewrite H7 in *.
  inversion H2; subst. clear H2.
  inversion H4; subst. clear H4.
  generalize dependent v0. 
  induction H3; intros; try (simpl in H; contradiction).
  -
    inversion H6; auto.
  -
    apply StringMap_mapsto_in in H2. inversion_clear H1.
    contradiction.
  -
    inversion_clear H6.
    + apply StringMapFacts.empty_mapsto_iff in H7. destruct H7.
    + assert (l = l0). { apply StringMapFacts.MapsTo_fun with G x; auto. }
      subst l0. apply NatMapProperties.update_mapsto_iff in H9. destruct H9.
      * apply NatMapFacts.empty_mapsto_iff in H6. destruct H6.
      * destruct H6. apply NatMapFacts.MapsTo_fun with S l; auto.
  -
    simpl in H. inversion_clear H0. inversion_clear H1.
    inversion_clear H6. auto.
  -
    simpl in H. inversion_clear H0. inversion_clear H1.
    inversion_clear H6. assert (v = v1). apply IHEvalExpr; auto.
    subst v1; auto.
  -
    simpl in H. apply Classical_Prop.not_or_and in H. destruct H.
    inversion_clear H0. inversion_clear H1. inversion_clear H6.
    assert (S = S'). { apply no_side_effects_no_store_change_eq in H3_; auto. }
    assert ((NatMapProperties.update S (NatMap.empty Z)) = S'0).
    { apply no_side_effects_no_store_change_eq in H1; auto. }
    subst S'. rewrite H9 in *. clear H9.
    assert (v1 = v3). { apply IHEvalExpr1; auto. }
    assert (v2 = v4). { apply IHEvalExpr2; auto. }
    subst v3 v4; auto.
Qed.


Lemma MSub_num_num : forall p e z ef,
  MSub p e (Num z) ef ->
  ef = Num z.
Proof.
  intros. inversion H; auto. Qed.


Lemma macrosubst_num_num : forall ps es z ef,
  MacroSubst ps es (Num z) ef ->
  ef = Num z.
Proof.
  intros. remember (Num z) as e. induction H; subst; auto.
  apply MSub_num_num in H. subst ef.
  apply IHMacroSubst; auto.
Qed.


Inductive ExprNoNamesIn : expr -> list string -> Prop :=
  | NNI_Num : forall z ps,
    ExprNoNamesIn (Num z) ps
  | NNI_Var : forall x ps,
    ~ In x ps ->
    ExprNoNamesIn (Var x) ps
  | NNI_ParenExpr : forall e0 ps,
    ExprNoNamesIn e0 ps ->
    ExprNoNamesIn (ParenExpr e0) ps
  | NNI_UnExpr : forall uo e0 ps,
    ExprNoNamesIn e0 ps ->
    ExprNoNamesIn (UnExpr uo e0) ps
  | NNI_BinExpr : forall bo e1 e2 ps,
    ExprNoNamesIn e1 ps ->
    ExprNoNamesIn e2 ps ->
    ExprNoNamesIn (BinExpr bo e1 e2) ps
  | NNI_Assign : forall x e0 ps,
    ~ In x ps ->
    ExprNoNamesIn e0 ps ->
    ExprNoNamesIn (Assign x e0) ps
  | NNI_CallOrInvocation : forall x es ps,
    ~ In x ps ->
    ExprNoNamesInArgs es ps ->
    ExprNoNamesIn (CallOrInvocation x es) ps
with ExprNoNamesInArgs : list expr -> list string -> Prop :=
  | NNIA_nil : forall ps,
    ExprNoNamesInArgs nil ps
  | NNIA_cons: forall e es ps,
    ExprNoNamesIn e ps ->
    ExprNoNamesInArgs (e::es) ps.


Definition unop_eq (uo1 : unop) (uo2 : unop) : bool :=
  match uo1 with
  | Positive => match uo2 with
    | Positive => true
    | Negative => false
    end

  | Negative => match uo2 with
    | Positive => false
    | Negative => true
    end
end.


Lemma unop_eq_refl : forall uo,
  unop_eq uo uo = true.
Proof.
  intros. induction uo; auto. Qed.


Definition binop_eq (bo1 : binop) (bo2 : binop) : bool :=
  match bo1 with
  | Plus => match bo2 with
    | Plus => true
    | Sub => false
    | Mul => false
    | Div => false
  end

  | Sub => match bo2 with
    | Plus => false
    | Sub => true
    | Mul => false
    | Div => false
  end

  | Mul => match bo2 with
    | Plus => false
    | Sub => false
    | Mul => true
    | Div => false
  end

  | Div => match bo2 with
    | Plus => false
    | Sub => false
    | Mul => false
    | Div => true
  end
end.


(* This is just syntactically equal *)
Fixpoint expr_equal (e1: expr) (e2: expr) : Prop :=
  match e1 with
  | Num z1 => match e2 with
    | Num z2 => if (z1 =? z2)%Z then True else False
    | _ => False
    end

  | Var x => match e2 with
    | Var y => if (x =? y)%string then True else False
    | _ => False
    end

  | ParenExpr e10 => match e2 with
    | ParenExpr e20 => expr_equal e10 e20
    | _ => False
    end

  | UnExpr uo1 e10 => match e2 with
    | UnExpr uo2 e20 => if (unop_eq uo1 uo2)
      then expr_equal e10 e20
      else False
    | _ => False
    end

  | BinExpr bo1 e11 e12 => match e2 with
    | BinExpr bo2 e21 e22 => if (binop_eq bo1 bo2) then
      expr_equal e11 e21 /\ expr_equal e12 e22
      else False
    | _ => False
    end

  | Assign x e10 => match e2 with
    | Assign y e20 => if (x =? y)%string then
      expr_equal e10 e20
      else False
    | _ => False
    end

  (* FIXME *)
  | CallOrInvocation x es => False
end.


Lemma binop_eq_refl : forall bo,
  binop_eq bo bo = true.
Proof.
  intros. induction bo; auto. Qed.



Scheme MacroSubst_EvalArgs := Induction for MacroSubst Sort Prop
with EvalArgs_MacroSubst := Induction for EvalArgs Sort Prop.



Lemma no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst :
  forall mexpr,
  (* The macro body must not have side-effects *)
  ~ ExprHasSideEffects mexpr ->
  forall F M,
  (* The macro must not contain a macro invocation *)
  NoMacroInvocations mexpr F M->
  forall Ecaller,
  (* The macro body must not rely on variables from the caller's scope.
     Global variables, however, are allowed. *)
  NoVarsInEnvironment mexpr Ecaller ->
  forall es,
  Forall (fun e => ~ExprHasSideEffects e) es ->
  (* The macro arguments must not contain a macro invocation,
     but they may contain variables from the caller's environment *)
  NoMacroInvocationsArgs es F M ->
  forall S G psf vs S' Ef Sargs l,
  (* The arguments can be evaluated to create a function environment *)
  EvalArgs S Ecaller G F M psf es vs S' Ef Sargs l ->
  (* We will prove that S = S' since there are no side-effects.
     S' and Sargs must be distinct so that we don't overwrite pre-existing
     L-values *)
  NatMapProperties.Disjoint S' Sargs ->
  forall v S'''0,
  (* The function body can be evaluated using call-by-value *)
  EvalExpr (NatMapProperties.update S' Sargs) Ef G F M mexpr v S'''0 ->
  forall psm ef,
  (* The arguments can be substituted into the expression body *)
  MacroSubst psm es mexpr ef ->
  forall v0 S''',
  (* The expression can be evaluated using call-by-name *)
  EvalExpr S Ecaller G F M ef v0 S''' ->
  (* The result of evaluation should be equal *)
  v = v0.
Proof.


  (* Attempt 4: Induction over mexpr followed by case-analysis on es *)
  induction mexpr.
  -
    intros. apply macrosubst_num_num in H7. subst ef.
    inversion H6. inversion H8. subst. auto.
  -
    destruct es.
    + admit.
    + inversion_clear H1. intro. inversion_clear H1.
      intro. inversion_clear H1. intros.
      inversion H9. subst. inversion H1. subst.
      induction e.
      inversion H14. subst. apply macrosubst_num_num in H17. subst ef.
      inversion H10. inversion H13. subst.


  (* (* Attempt 3: Induction over vs *)
  induction vs.
  - admit.
  - intros. eapply IHvs; eauto.
    (* Gets close... *) *)


  (* (* Attempt 2: Induction over es *)
  induction es.
  - (* Easy*) admit.
  - intros. eapply IHes; eauto. inversion_clear H4.
    inversion_clear H7.
    (* Can't prove 3 and 4 *) *)
  

  (*
  (* Attempt 1: Induction over the argument evaluation *)
  intros until l. intro. assert (S=S').
  { apply no_side_effects_no_store_change_evalargs_eq in H4; auto. }
  subst S'.
  
  induction H4.
  - intros. (* Should be easy *) admit.
  - intros. apply IHEvalArgs with S'''0 psm ef S'''; auto.

  intros until ef. intros H4. induction H4.
  - intros. apply no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil with
    mexpr F M Ecaller mexpr S G S''' S' Ef Sargs l S'''0; auto.
    + constructor.
    + inversion H5. subst. auto.
  (* TODO: Induction on e and mexpr? I think that could work... *)
  - inversion_clear H2. induction e, mexpr;
    try (simpl in H6; contradiction); try (simpl in H; contradiction).
    + admit.
    + admit. *)
Abort.


Theorem transform_expr_sound_mut_v_s : forall M F e F' e',
  TransformExpr M F e F' e' ->
  (* The proof will not work if these variables were introduced sooner.
     Doing so would interfere with the induction hypothesis *)
  forall S E G v1 v2 S'1 S'2,
    EvalExpr S E G F M e v1 S'1 ->
    EvalExpr S E G F' M e' v2 S'2 ->
    v1 = v2 /\ S'1 = S'2.
Proof.
  apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
    forall S E G v1 v2 S'1 S'2,
      EvalExpr S E G F M e v1 S'1 ->
      EvalExpr S E G F' M e' v2 S'2 ->
      v1 = v2 /\ S'1 = S'2)
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
    forall S Ecaller G ps1 vs1 vs2 S'1 S'2 Ef1 Ef2 Sargs1 Sargs2 l1 l2,
      EvalArgs S Ecaller G F M ps1 es vs1 S'1 Ef1 Sargs1 l1 ->
      EvalArgs S Ecaller G F' M ps1 es' vs2 S'2 Ef2 Sargs2 l2 ->
      l1 = l2 /\ Ef1 = Ef2 /\ Sargs1 = Sargs2 /\ vs1 = vs2 /\ S'1 = S'2)
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
    forall S E G S'1 S'2,
      EvalStmt S E G F M stmt S'1 ->
      EvalStmt S E G F' M stmt' S'2 ->
      S'1 = S'2
      )); intros; auto.
  -
    inversion H. inversion H0; subst. auto.
  -
    inversion H; subst.
    + inversion H0; subst.
      * apply StringMapFacts.find_mapsto_iff in H2, H3.
        rewrite H3 in H2. inversion H2; subst.
        apply NatMapFacts.find_mapsto_iff in H8, H10.
        rewrite H10 in H8. inversion H8. auto.
      * apply StringMap_mapsto_in in H2. contradiction.
    + inversion H0; subst.
      * apply StringMap_mapsto_in in H4. contradiction.
      * apply StringMapFacts.find_mapsto_iff in H3, H5.
        rewrite H5 in H3. inversion H3; subst.
        apply NatMapFacts.find_mapsto_iff in H9, H12.
        rewrite H12 in H9. inversion H9. auto.
  -
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v1 v2 S'1 S'2; auto.
  -
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v v0 S'1 S'2; auto.
    subst. auto.
  -
    inversion_clear H1. inversion_clear H2.
    destruct H with S E G v0 v4 S' S'0; auto.
    subst. destruct H0 with S'0 E G v3 v5 S'1 S'2; subst; auto.
  -
    inversion H0; subst.
    + inversion H1; subst.
      * apply StringMapFacts.find_mapsto_iff in H4, H5.
        rewrite H5 in H4. inversion H4; subst.
        destruct H with S E G v1 v2 S' S'0; auto.
        subst. auto.
      * apply StringMap_mapsto_in in H4. contradiction.
    + inversion H1; subst.
      * apply StringMap_mapsto_in in H6. contradiction.
      * apply StringMapFacts.find_mapsto_iff in H5, H7.
        rewrite H7 in H5. inversion H5; subst.
        destruct H with S E G v1 v2 S' S'0; auto.
        subst. auto.
  -
    inversion_clear H2. inversion_clear H3.
    + 
      assert (StringMap.MapsTo x (params, fstmt', fexpr') F').
      { subst. apply StringMapFacts.add_mapsto_iff. left. auto. }
      apply StringMapFacts.find_mapsto_iff in H15, H3.
      rewrite H3 in H15. inversion H15. clear H15.
      apply StringMapFacts.find_mapsto_iff in m, H5.
      rewrite H5 in m. inversion m.
      subst.
      destruct H with S E G params1 vs vs0 S' S'0 Ef Ef0 Sargs Sargs0 l l0; auto.
      destruct H15. destruct H21. destruct H25. subst.
      destruct H0 with (NatMapProperties.update S'0 Sargs0) Ef0 G S''' S'''0 ; auto.
      destruct H1 with S''' Ef0 G v1 v2 S'''' S''''0; auto. subst.
      apply NatMap_Equal_eq_iff in H14, H24. subst. auto.
    + apply StringMap_mapsto_in in H2. contradiction.
    + apply StringMap_mapsto_in in H4. contradiction.
  -
    inversion H1. inversion H2.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + inversion H2.
      subst S0 E0 G0 F0 M0 x0 es0 v1 S'1.
      subst S1 E1 G1 F1 M1 x1 es1 v2 S'''''.
      * (* This is it *)
        
        (* No side-effects in function *)
        assert (mexpr = mexpr').
        { apply nomacroinvocations_transformexpr_no_change with F M F'; auto. }
        subst mexpr'.
        assert ( (params1, fstmt, fexpr) = (params, Skip, mexpr) ).
        { apply StringMapFacts.MapsTo_fun with F' fname; auto.
          rewrite e. apply StringMapFacts.add_mapsto_iff. left. auto. }
        inversion H3. subst params1 fstmt fexpr. clear H3.
        assert (Forall (fun e : expr => ~ ExprHasSideEffects e) es').
        { apply no_side_effects_Forall_no_side_effects with
          es M F F'; auto. }
        assert (S = S'0).
        { apply no_side_effects_no_store_change_evalargs_eq in H22; auto. }
        subst S'0. apply skip_no_side_effects_eq in H27. subst S'''.
        assert (S'' = S'''').
        { apply no_side_effects_no_store_change_eq in H33; auto. }
        subst S''''.
        assert (NatMap.Equal S (NatMapProperties.restrict S'' S)).
        { rewrite H26. apply NatMap_disjoint_restrict_Equal; auto. }
        rewrite <- H4 in H36. apply NatMap_Equal_eq_iff in H36. rewrite H36.
        
        (* No side-effects in macro *)
        assert (es = es').
        { apply nomacroinvocationsargs_transformargs_no_change with F M F'; auto. }
        subst es'.
        assert ( (params, mexpr) = (params0, mexpr0) ).
        { apply StringMapFacts.MapsTo_fun with M x; auto. }
        symmetry in H8. inversion H8. subst params0 mexpr0. clear H8.
        assert (~ ExprHasSideEffects ef).
        (* TODO: Fix this; probably need to add some things as premises in transformation *)
        { apply no_side_effects_macrosubst_no_side_effects with mexpr params es; auto. }
        assert (S = S').
        { apply no_side_effects_no_store_change_eq in H16; auto; auto. }
        subst S'. apply NatMap_Equal_eq_iff in H4.
        assert (NoVarsInEnvironment mexpr E).
        { apply n2 with S G v S; auto. }
        split.
        -- admit.
        -- auto.
        
        (* Issues:
           1) Proving value equivalence
           2) Coq doesn't treatin FMap.Equal as the same thing as Logic.eq
           
           Solutions:
           1) ???
           2) Just use an axiom stating that Equal implies eq. *) 
        
        
      * apply StringMap_mapsto_in in H19. contradiction. 
  - inversion H. inversion H0. subst. split; auto.
  - inversion H1. inversion H2.
    destruct H with S Ecaller G v v0 Snext Snext0; auto. subst. inversion H31. subst.
    destruct H0 with Snext0 Ecaller G ps vs vs0 S'1 S'2 Ef' Ef'0 Sargs' Sargs'0 l l0; auto.
    destruct H4. destruct H8. destruct H9. subst.
    split; auto.
  - inversion H. inversion H0. subst. auto.
Abort.


