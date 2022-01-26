(* IDEA:
   First practice JUST transforming the F by adding the new function definitions to it.
   It may be better to instead of directly adding new definitions to F, to collect all
   the new definitions into their own map, then update the current map with the map
   of new function in the returned map. This would allow use to add assertions about the two
   maps being disjoint, which would in turn allow us to prove the soundness of function
   lookup. *)

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


Theorem no_side_effects_no_store_change_arg_eval : forall S E G F M es S' vs,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M es vs S' ->
  NatMap.Equal S S'.
Proof.
  intros. induction H0.
  - reflexivity.
  - inversion H. apply no_side_effects_no_store_change in H0.
    rewrite H0. apply IHEvalArgs. assumption. assumption.
Qed.


Theorem no_side_effects_no_store_change_arg_eval_eq : forall S E G F M es S' vs,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M es vs S' ->
  S = S'.
Proof.
  intros. induction H0.
  - reflexivity.
  - inversion H. apply no_side_effects_no_store_change_eq in H0.
    rewrite H0. apply IHEvalArgs. assumption. assumption.
Qed.


Lemma no_side_effects_evalargs_evalargs: forall S E G F M es S' vs,
  Forall (fun e => ~ ExprHasSideEffects e ) es ->
  EvalArgs S E G F M es vs S' ->
  EvalArgs S E G F M es vs S.
Proof.
  intros. induction H0.
  - apply EvalArgs_nil. assumption.
  - inversion H; subst. apply EvalArgs_cons with Snext.
    + assumption.
    + apply no_side_effects_no_store_change_eq in H0; subst.
      * apply IHEvalArgs. assumption.
      * assumption.
Qed.


Lemma skip_no_side_effects : forall S E G F M S',
  EvalStmt S E G F M Skip S' ->
  NatMap.Equal S S'.
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
      (fun Sprev Ecaller G F M es vs Snext (h : EvalArgs Sprev Ecaller G F M es vs Snext) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalArgs Sprev Ecaller G (StringMap.add x fdef F) M es vs Snext)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' MP ef; auto.
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
      (fun Sprev Ecaller G F M es vs Snext (h : EvalArgs Sprev Ecaller G F M es vs Snext) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.update F F') M es vs Snext)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs; auto.
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
  - apply E_MacroInvocation with params mexpr M' MP ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma evalargs_notin_F_add_evalargs : forall S E G F M es vs S',
  EvalArgs S E G F M es vs S' ->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalArgs S E G (StringMap.add x fdef F) M es vs S'.
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
      (fun Sprev Ecaller G F M es vs Snext (h : EvalArgs Sprev Ecaller G F M es vs Snext) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalArgs Sprev Ecaller G (StringMap.add x fdef F) M es vs Snext)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' MP ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma evalargs_disjoint_update_F_evalargs : forall S E G F M es vs S',
  EvalArgs S E G F M es vs S' ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalArgs S E G (StringMapProperties.update F F') M es vs S'.
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
      (fun Sprev Ecaller G F M es vs Snext (h : EvalArgs Sprev Ecaller G F M es vs Snext) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.update F F') M es vs Snext)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs; auto.
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
  - apply E_MacroInvocation with params mexpr M' MP ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Theorem side_effect_free_function_no_side_effects :
  forall S E G F M x es params fstmt fexpr ls
         Sargs S' S'' S''' Ef S'''' S''''' v vs,
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  ~ ExprHasSideEffects fexpr ->
  
  fstmt = Skip ->
  ~ StringMap.In x M ->
  StringMap.MapsTo x (params, fstmt, fexpr) F ->
  NoDup params ->
  EvalArgs S E G F M es vs S' ->
  StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->
  NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) ->
  NatMapProperties.Disjoint S' Sargs ->
  NatMap.Equal S'' (NatMapProperties.update S' Sargs) ->
  EvalStmt S'' Ef G F M fstmt S''' ->
  EvalExpr S''' Ef G F M fexpr v S'''' ->
  NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
  EvalExpr S E G F M (CallOrInvocation x es) v S''''' ->
  NatMap.Equal S''''' S.
Proof.
  intros. subst. apply no_side_effects_no_store_change_arg_eval in H5.
  - apply skip_no_side_effects in H10. apply no_side_effects_no_store_change in H11.
    + assert (HS: NatMap.Equal S
                  (NatMapProperties.restrict (NatMapProperties.update S Sargs) S)).
      { apply NatMap_disjoint_restrict_Equal. rewrite <- H5 in H8. assumption. }
      rewrite <- H5 in H8. rewrite H9 in H10. rewrite <- H10 in H11.
      rewrite <- H11 in H12. rewrite <- H5 in H12.
      rewrite <- HS in H12. assumption.
    + assumption.
  - assumption.
Qed.


Lemma forall_es_combine_forall_snd: forall A B P (ks : list A) (es : list B) pair,
  Forall (fun e => ~ P e) es ->
  In pair (combine ks es) ->
  ~ P (snd pair).
Proof.
  intros.
  assert (In (snd pair) (snd (split (combine ks es)))).
  apply in_split_r. assumption. destruct pair.
  apply in_combine_r in H0. simpl.
  rewrite Forall_forall in H. apply H. assumption.
Qed.


Theorem no_side_effects_msub_no_side_effects : forall mexpr params es MP,
  ~ ExprHasSideEffects mexpr ->
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  MP = (combine params es) ->
  ~ ExprHasSideEffects (msub MP mexpr).
Proof.
  intros.
  induction mexpr; auto.
  - simpl. destruct lookup_macro_parameter eqn: Hfind.
    + unfold lookup_macro_parameter in Hfind.
      apply List.find_some in Hfind.
      apply forall_es_combine_forall_snd with (ks:=params) (es:=es).
      assumption. rewrite H1 in Hfind. apply Hfind.
    + auto.
  - simpl in *. apply Classical_Prop.not_or_and in H. destruct H.
    apply Classical_Prop.and_not_or. split.
    + apply IHmexpr1. assumption.
    + apply IHmexpr2. assumption.
  - simpl in H. contradiction.
Qed.


Theorem side_effect_free_macro_no_side_effects :
  forall S E G F M x params es mexpr M' MP ef S' v,
  StringMap.MapsTo x (params, mexpr) M ->
  ~ ExprHasSideEffects mexpr ->
  M' = StringMap.remove x M ->
  NoDup params ->
  Forall (fun e => ~ExprHasSideEffects e) es ->
  MP = combine params es ->
  ef = msub MP mexpr ->
  EvalExpr S E G F M' ef v S' ->
  EvalExpr S E G F M (CallOrInvocation x es) v S' ->
  NatMap.Equal S S'.
Proof.
  intros.
  apply no_side_effects_no_store_change in H6. assumption.
  rewrite H5 in H6. apply no_side_effects_msub_no_side_effects
    with (params:=params) (es:=es) (MP:=MP) in H0.
  - rewrite <- H5 in H0. assumption.
  - assumption.
  - assumption.
Qed.


Example transform_side_effect_free_macro_sound :
  forall S E G F F' M x y params es mexpr M' MP ef S0' S' (v : Z)
         ls Sargs S'' S''' Ef S'''' S''''' v vs,
  StringMap.MapsTo x (params, mexpr) M ->
  ~ ExprHasSideEffects mexpr ->
  M' = StringMap.remove x M ->
  NoDup params ->

  Forall (fun e => ~ExprHasSideEffects e) es ->
  MP = combine params es ->
  ef = msub MP mexpr ->
  EvalExpr S E G F M' ef v S0' ->
  EvalExpr S E G F M (CallOrInvocation x es) v S0' ->

  Forall (fun e => ~ ExprHasSideEffects e) es ->
  ~ ExprHasSideEffects mexpr ->
  ~ StringMap.In y M ->

  (* Function name maps to some function *)
  StringMap.MapsTo y (params, Skip, mexpr) F' ->
  (* Parameters should all be unique *)
  NoDup params ->
  (* Evaluate the function's arguments *)
  EvalArgs S E G F' M es vs S' ->
  (* Create the function environment *)
  StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->
  (* Create a store for mapping L-values to the arguments to in the store *)
  NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) ->
  (* All the L-values used in the argument store do not appear in the original store *)
  NatMapProperties.Disjoint S' Sargs ->
  (* Combine the argument store into the original store *)
  NatMap.Equal S'' (NatMapProperties.update S' Sargs) ->
  (* Evaluate the function's body *)
  EvalStmt S'' Ef G F' M Skip S''' ->
  EvalExpr S''' Ef G F' M mexpr v S'''' ->
  (* Only keep in the store the L-value mappings that were there when
     the function was called; i.e., remove from the store all mappings
     whose L-value is in Ef/Sargs. *)
  NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
  EvalExpr S E G F' M (CallOrInvocation y es) v S''''' ->
  NatMap.Equal S0' S'''''.
Proof.
  intros.
  apply side_effect_free_macro_no_side_effects
    with (params:=params) (mexpr:=mexpr) (M:=M) (M':=M') (MP:=MP) (ef:=ef) in H7;
      try assumption.
  apply side_effect_free_function_no_side_effects with
    (params:=params) (fstmt:=Skip) (fexpr:=mexpr) (ls:=ls) (Sargs:=Sargs) (S':=S')
    (S'':=S'') (S''':=S''') (Ef:=Ef) (S'''':=S'''') (vs:=vs) in H21;
      try assumption; try reflexivity.
  rewrite <- H7. rewrite H21. reflexivity.
Qed.


(* This proof is easy right now because we only have Skip statements *)
Lemma mapsto_transformstmt_mapsto : forall x fdef F M stmt F' stmt', 
  StringMap.MapsTo x fdef F ->
  TransformStmt M F stmt F' stmt' ->
  StringMap.MapsTo x fdef F'.
Proof.
  intros. induction H0. assumption.
Qed.


(* This proof is easy right now because we only have Skip statements *)
Lemma evalstmt_transformargs_evalstmt : forall S E G F M stmt S' F' stmt',
  EvalStmt S E G F M stmt S' ->
  TransformStmt M F stmt F' stmt' ->
  EvalStmt S E G F' M stmt S'.
Proof.
  intros. induction H0. assumption.
Qed.


Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformArgs_mut := Induction for TransformArgs Sort Prop
with TransformStmt_mut := Induction for TransformStmt Sort Prop.


(* Attempt 2: Induction over the transformation with schema *)
Theorem transform_expr_sound_mut : forall M F e F' e',
  TransformExpr M F e F' e' ->
  (* The proof will not work if these variables were introduced sooner.
     Doing so would interfere with the induction hypothesis *)
  forall S E G v S',
    EvalExpr S E G F M e v S' ->
    EvalExpr S E G F' M e' v S'.
Proof.
  intros M F e F' e' H. apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
    forall S E G v S',
      EvalExpr S E G F M e v S' ->
      EvalExpr S E G F' M e' v S')
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
    forall S Ecaller G vs S',
      EvalArgs S Ecaller G F M es vs S' ->
      EvalArgs S Ecaller G F' M es' vs S')
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
    forall S E G S',
      EvalStmt S E G F M stmt S' ->
      EvalStmt S E G F' M stmt' S')); auto.
  - intros. inversion_clear H1. apply E_ParenExpr. apply H0; auto.
  - intros. inversion_clear H1. apply E_UnExpr. apply H0; auto.
  - intros. inversion_clear H2. apply E_BinExpr with S'0.
    + subst. apply evalexpr_disjoint_update_F_evalexpr; auto.
    + subst. apply H1. apply evalexpr_disjoint_update_F_evalexpr. auto. auto.
  - intros. inversion_clear H1.
    + apply E_Assign_Local with l S'0; auto.
    + apply E_Assign_Global with l S'0; auto.
  - intros. inversion_clear H3.
    + apply StringMapFacts.find_mapsto_iff in m.
      apply StringMapFacts.find_mapsto_iff in H5.
      rewrite H5 in *. inversion m. subst. clear m.
      apply E_FunctionCall with params fstmt' fexpr' ls Ef Sargs S'0 S'' S''' S'''' vs; auto.
      * apply StringMapFacts.add_mapsto_iff. left; auto.
      * apply evalargs_notin_F_add_evalargs; auto.
        apply evalargs_disjoint_update_F_evalargs; auto.
        apply evalargs_disjoint_update_F_evalargs; auto.
      * apply evalstmt_notin_F_add_evalstmt; auto.
        apply evalstmt_disjoint_update_F_evalstmt; auto.
        apply H1.
        apply evalstmt_disjoint_update_F_evalstmt; auto.
      * apply evalexpr_notin_F_add_evalexpr; auto.
        apply H2.
        apply evalexpr_disjoint_update_F_evalexpr; auto.
        apply evalexpr_disjoint_update_F_evalexpr; auto.
    + apply StringMap_mapsto_in in H4. contradiction.
  - intros. inversion_clear H1.
    + apply StringMap_mapsto_in in m. contradiction.
    + apply StringMapFacts.find_mapsto_iff in m.
      apply StringMapFacts.find_mapsto_iff in H2.
      rewrite H2 in *. inversion m. subst. clear m.
      assert (
        EvalArgs S E G F0 M0 es vs S' /\
        StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) /\
        NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) /\
        NatMapProperties.Disjoint S' Sargs /\
        NatMap.Equal S'' (NatMapProperties.update S' Sargs) /\
        EvalStmt S'' Ef G F0 M0 Skip S''' /\
        EvalExpr S''' Ef G F0 M0 mexpr v0 S'''' /\
        NatMap.Equal S''''' (NatMapProperties.restrict S'''' S)
     ). { apply a. }
     destruct H1. destruct H3. destruct H5. destruct H6. destruct H8. destruct H9.
     destruct H10.
      apply E_FunctionCall with
        (params:=params) (fstmt:=Skip) (fexpr:=mexpr) (ls:=ls)
        (Ef:=Ef) (Sargs:=Sargs) (S':=S') (S'':=S'') (S''':=S''') (S'''':=S'''')
        (vs:=vs); auto.
      * apply StringMapFacts.add_mapsto_iff. left; auto.
      * apply evalargs_notin_F_add_evalargs; auto.
      * apply evalstmt_notin_F_add_evalstmt; auto.
        apply evalstmt_disjoint_update_F_evalstmt; auto.
      * apply evalexpr_notin_F_add_evalexpr; auto.
        apply evalexpr_disjoint_update_F_evalexpr; auto.
      *
        (* Here is where we prove that they evaluate to the same state *)
        assert (~ ExprHasSideEffects (msub (combine params es) mexpr)).
        { apply no_side_effects_msub_no_side_effects with params es; auto. }
        apply no_side_effects_no_store_change in H7; auto.
        apply no_side_effects_no_store_change_arg_eval in H1; auto.
        apply skip_no_side_effects in H9; auto.
        apply no_side_effects_no_store_change in H10; auto.
        rewrite <- H7. rewrite <- H10. rewrite <- H9. rewrite H8. rewrite <- H1.
        apply NatMap_disjoint_restrict_Equal. rewrite H1. auto.
  - intros. inversion_clear H2. apply EvalArgs_cons with Snext.
    + subst. apply evalexpr_disjoint_update_F_evalexpr; auto.
    + subst. apply H1; auto using evalargs_disjoint_update_F_evalargs.
Qed.
