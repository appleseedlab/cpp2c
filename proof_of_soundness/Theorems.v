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
  - intros. inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
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
  - intros. inversion_clear H0. apply StringMap_mapsto_in in m. contradiction.
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
    (* Induction rule for TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
    forall S E G v1 v2 S'1 S'2,
      EvalExpr S E G F M e v1 S'1 ->
      EvalExpr S E G F' M e' v2 S'2 ->
      v1 = v2 /\ S'1 = S'2)
    (* Induction rule for TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
    forall S Ecaller G ps1 vs1 vs2 S'1 S'2 Ef1 Ef2 Sargs1 Sargs2 l1 l2,
      EvalArgs S Ecaller G F M ps1 es vs1 S'1 Ef1 Sargs1 l1 ->
      EvalArgs S Ecaller G F' M ps1 es' vs2 S'2 Ef2 Sargs2 l2 ->
      l1 = l2 /\ Ef1 = Ef2 /\ Sargs1 = Sargs2 /\ vs1 = vs2 /\ S'1 = S'2)
    (* Induction rule for TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
    forall S E G S'1 S'2,
      EvalStmt S E G F M stmt S'1 ->
      EvalStmt S E G F' M stmt' S'2 ->
      S'1 = S'2
      )); intros; auto.
  - (* Num *)
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

  - (* ParenExpr *)
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v1 v2 S'1 S'2; auto.

  - (* UnExpr *)
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v v0 S'1 S'2; auto.
    subst. auto.

  - (* BinExpr *)
    inversion_clear H1. inversion_clear H2.
    destruct H with S E G v0 v4 S' S'0; auto.
    subst. destruct H0 with S'0 E G v3 v5 S'1 S'2; subst; auto.

  - (* Assign *)
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
  - (* Function call *)
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

  - (* Object like macro without side-effects, shared variables with the caller environment,
       or nested macro invocations *)
    inversion H0. inversion H1.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + inversion H1.
      subst S0 E0 G0 F0 M0 x0 es v1 S'1.
      subst S1 E1 G1 F1 M1 x1 es0 v2 S'''''.
      * (* Proof of equivalence *)

        (* Prove that the macro body does not change after transformation *)
        assert (mexpr = mexpr').
        { apply nomacroinvocations_transformexpr_no_change with F M F'; auto. }
        subst mexpr'.

        (* No side-effects in function *)

        (* Prove that the definition that we know the function maps to
           is the same one that we added during the transformation *)
        assert ( (params1, fstmt, fexpr) = (nil, Skip, mexpr) ).
        { apply StringMapFacts.MapsTo_fun with F' fname; auto.
          rewrite e. apply StringMapFacts.add_mapsto_iff. left. auto. }
        inversion H2. subst params1 fstmt fexpr. clear H2.

        (* Add to the context all the premises we get from evaluating an
           empty argument list *)
        inversion H21. subst Sprev E G0 F0 M0 vs S'0 Ef Sargs l.

        (* Prove that there are no side-effects caused by the skip statement *)
        apply skip_no_side_effects_eq in H26. subst S'''.

        (* Prove that there are no side-effects cause by the return expression *)
        assert (S'' = S''''). { apply no_side_effects_no_store_change_eq in H32; auto. }
        subst S''''.

        (* Prove that after freeing the memort allocated for function environment,
           the store reverts back to its original state *)
        assert (NatMap.Equal S (NatMapProperties.restrict S'' S)).
        { rewrite H25. apply NatMap_disjoint_restrict_Equal; auto. }
        rewrite <- H2 in H35. apply NatMap_Equal_eq_iff in H35. subst S'2.

        (* No side-effects in macro *)

        (* Prove that the definition that we know the macro maps to
           is the same one we asserted in the transformation *)
        assert ( (params, mexpr) = (params0, mexpr0) ).
        { apply StringMapFacts.MapsTo_fun with M x; auto. }
        inversion H3. subst params0 mexpr0. clear H3.

        (* Prove that after macro substitution, the macro body still
           does not have side-effects *)
        assert (~ ExprHasSideEffects ef).
        { apply no_side_effects_macrosubst_no_side_effects with mexpr params nil; auto. }

        (* Prove that the macro invocation does not have side-effects *)
        assert (S = S').
        { apply no_side_effects_no_store_change_eq in H15; auto; auto. }
        subst S'.

        (* Use one of our premises to assert that the macro does not contain
           variables from the caller environment *)
        (* NOTE: We should probably add the environment to the transformation
           relation so that we don't have to use such a generous premise *)
        assert (NoVarsInEnvironment mexpr Ecaller).
        { apply n1 with S G v S; auto. }
        split.
        --
          (* Prove that the expression will result in the same value
             under call-by-name and call-by-value *)
          apply no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil with
            mexpr F' M' Ecaller mexpr S G S S (StringMap.empty nat) (NatMap.empty Z) 0 S'';
              auto.
            ++ (* Prove that the macro body does contain a macro invocation *)
               subst M'. apply nomacroinvocations_remove_nomacroinvocations.
               apply nomacroinvocations_transformexpr_nomacroinvocations with F mexpr; auto.
            ++ constructor.
            ++ (* Prove that macro expression evaluation works the same
                  under an updated function table *)
               inversion H12. subst ef mexpr0 params.
               subst F'. apply evalexpr_notin_F_add_evalexpr; auto.
            ++ constructor.
            ++ (* Prove that function expression evaluation works the same
                  under an updated macro table *)
               subst S'' M'. apply nomacroinvocations_remove_evalexpr; auto.
               apply nomacroinvocations_transformexpr_nomacroinvocations with F mexpr; auto.
        -- auto.
      * apply StringMap_mapsto_in in H18. contradiction.
  - inversion H. inversion H0. subst. split; auto.
  - inversion H1. inversion H2.
    destruct H with S Ecaller G v v0 Snext Snext0; auto. subst. inversion H31. subst.
    destruct H0 with Snext0 Ecaller G ps vs vs0 S'1 S'2 Ef' Ef'0 Sargs' Sargs'0 l l0; auto.
    destruct H4. destruct H8. destruct H9. subst.
    split; auto.
  - inversion H. inversion H0. subst. auto.
Qed.


(* Issues:
           1) Proving evaluation equivalence under call-by-name and call-by-value
           2) Coq doesn't treat FMap.Equal as the same thing as Logic.eq

           Solutions:
           1) ???
           2) Just use an axiom stating that Equal implies eq. *) 
