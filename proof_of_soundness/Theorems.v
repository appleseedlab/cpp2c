Require Import
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  EvalRules
  Transformations.


Lemma NatMap_Empty_empty : forall (m : store),
  NatMap.Empty (elt:=Z) m ->
  NatMap.Equal m (NatMap.empty Z).
Proof.
  intros.
  unfold NatMap.Empty in H.
  apply NatMapProperties.elements_Empty in H.
  unfold NatMap.Equal. intros.
  rewrite NatMapFacts.elements_o. rewrite H. simpl.
  rewrite NatMapFacts.empty_o. reflexivity.
Qed.


Lemma StringMap_Empty_empty : forall (t : Type) (m : StringMap.t t),
  StringMap.Empty (elt:=_) m ->
  StringMap.Equal m (StringMap.empty _).
Proof.
  intros.
  unfold StringMap.Empty in H.
  apply StringMapProperties.elements_Empty in H.
  unfold StringMap.Equal. intros.
  rewrite StringMapFacts.elements_o. rewrite H. simpl.
  rewrite StringMapFacts.empty_o. reflexivity.
Qed.


Lemma NatMap_restrict_refl: forall (S : store),
  NatMap.Equal S (NatMapProperties.restrict S S).
Proof.
  intros. rewrite NatMapFacts.Equal_mapsto_iff.
  intros. rewrite NatMapProperties.restrict_mapsto_iff.
  split; intros.
  - (* -> *)
    split.
    + apply H.
    + apply NatMapFacts.find_mapsto_iff in H.
      apply NatMapFacts.in_find_iff. unfold not.
      intros. rewrite H0 in H. discriminate H.
  - (* <- *)
    apply H.
Qed.


Lemma no_side_effects_no_store_change : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  ExprEval S E G F M e v S' ->
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
    apply demorgan in H.
    rewrite <- IHE1_1 in IHE1_2.
    apply IHE1_2.  apply H. apply H.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Lemma NatMap_mapsto_in: forall (S : store) l v,
  NatMap.MapsTo l v S -> NatMap.In l S.
Proof.
  intros.
  apply NatMapFacts.find_mapsto_iff in H.
  apply NatMapFacts.in_find_iff. unfold not. intros.
  rewrite H0 in H. discriminate.
Qed.


Lemma StringMap_mapsto_in: forall (t : Type) (m : StringMap.t t) k e,
  StringMap.MapsTo k e m -> StringMap.In k m.
Proof.
  intros.
  apply StringMapFacts.find_mapsto_iff in H.
  apply StringMapFacts.in_find_iff. unfold not. intros.
  rewrite H0 in H. discriminate.
Qed.


Lemma NatMap_add_unique_then_restrict_no_change : forall (S : store) l v,
  ~ NatMap.In l S ->
  NatMap.Equal S (NatMapProperties.restrict (NatMapProperties.update S ( NatMap.add l v (NatMap.empty Z))) S).
Proof.
  intros. rewrite NatMapFacts.Equal_mapsto_iff.
  split.
  - intros. apply NatMapProperties.restrict_mapsto_iff. split.
    + apply NatMapProperties.update_mapsto_iff. right. split.
      * assumption.
      * apply NatMapFacts.not_find_in_iff in H as HfindlinS.
        unfold not. rewrite NatMapFacts.add_in_iff. intros.
        destruct H1.
        -- apply NatMapFacts.find_mapsto_iff in H0 as HfindkinS.
           rewrite <- H1 in HfindkinS. rewrite HfindkinS in HfindlinS. discriminate.
        -- apply NatMapFacts.empty_in_iff in H1. apply H1.
    + apply NatMap_mapsto_in in H0. assumption.
  - intros. apply NatMapProperties.restrict_mapsto_iff in H0.
    destruct H0. apply NatMapProperties.update_mapsto_iff in H0.
    destruct H0.
    + apply NatMapFacts.add_mapsto_iff in H0.
      * destruct H0.
        -- destruct H0. rewrite <- H0 in H1. contradiction.
        -- destruct H0. apply NatMapFacts.empty_mapsto_iff in H2. destruct H2.
    + destruct H0. assumption.
Qed.


Theorem NatMap_disjoint_diff_Equal : forall (S1 : store) (S2 : store),
  NatMapProperties.Disjoint S1 S2 ->
  NatMap.Equal S1 (NatMapProperties.diff (NatMapProperties.update S1 S2) S2).
Proof.
  intros. apply NatMapFacts.Equal_mapsto_iff. intros. split.
  - intros. apply NatMapProperties.diff_mapsto_iff. split.
    + apply NatMapProperties.update_mapsto_iff. right. split.
      * assumption.
      * unfold NatMapProperties.Disjoint in H.
        apply NatMap_mapsto_in in H0. unfold not. intros. unfold not in H.
        apply H with k. split.
        -- assumption.
        -- assumption.
    + unfold NatMapProperties.Disjoint in H.
      apply NatMap_mapsto_in in H0. unfold not. intros. unfold not in H.
      apply H with k. split.
      * assumption.
      * assumption.
  - intros. apply NatMapProperties.diff_mapsto_iff in H0. destruct H0.
    apply NatMapProperties.update_mapsto_iff in H0. destruct H0.
    * apply NatMap_mapsto_in in H0. contradiction.
    * destruct H0. apply H0.
Qed.


Theorem NatMap_disjoint_restrict_Equal : forall (S1 : store) (S2 : store),
  NatMapProperties.Disjoint S1 S2 ->
  NatMap.Equal S1 (NatMapProperties.restrict (NatMapProperties.update S1 S2) S1).
Proof.
  intros.
  apply NatMapFacts.Equal_mapsto_iff. intros. split.
  - intros. apply NatMapProperties.restrict_mapsto_iff. split.
    + apply NatMapProperties.update_mapsto_iff. right. split.
      * assumption.
      * unfold NatMapProperties.Disjoint in H.
        apply NatMap_mapsto_in in H0. unfold not. intros. unfold not in H.
        apply H with k. split.
        -- assumption.
        -- assumption.
    + apply NatMap_mapsto_in in H0. assumption.
  - rewrite NatMapProperties.restrict_mapsto_iff.
    rewrite NatMapProperties.update_mapsto_iff.
    intros. destruct H0. destruct H0.
    + exfalso. unfold NatMapProperties.Disjoint in H. unfold not in H.
      apply H with k. split.
      * assumption.
      * apply NatMap_mapsto_in in H0. assumption.
    + destruct H0. assumption.
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


Theorem skip_no_side_effects : forall S E G F M S',
  StmtEval S E G F M Skip S' ->
  NatMap.Equal S S'.
Proof.
  intros. induction H. reflexivity.
Qed.


Theorem side_effect_free_function_no_side_effects :
  forall S E G F M x es params fstmt fexpr ls
         Sargs S' S'' S''' Ef S'''' S''''' v vs,
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  ~ ExprHasSideEffects fexpr ->
  fstmt = Skip ->
  ~ StringMap.In x M ->
  (* Function name maps to some function *)
  StringMap.MapsTo x (params, fstmt, fexpr) F ->
  (* Parameters should all be unique *)
  NoDup params ->
  (* Evaluate the function's arguments *)
  EvalArgs S E G F M es vs S' ->
  (* Create the function environment *)
  StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->
  (* Create a store for mapping L-values to the arguments to in the store *)
  NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) ->
  (* All the L-values used in the argument store do not appear in the original store *)
  NatMapProperties.Disjoint S' Sargs ->
  (* Combine the argument store into the original store *)
  NatMap.Equal S'' (NatMapProperties.update S' Sargs) ->
  (* Evaluate the function's body *)
  StmtEval S'' Ef G F M fstmt S''' ->
  ExprEval S''' Ef G F M fexpr v S'''' ->
  (* Only keep in the store the L-value mappings that were there when
     the function was called; i.e., remove from the store all mappings
     whose L-value is in Ef/Sargs. *)
  NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
  ExprEval S E G F M (CallOrInvocation x es) v S''''' ->
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


(* (* TODO: This will be very important, but I'm having a very hard time proving it *)
Lemma StringMap_no_side_effects_es_mapsto_no_side_effects :
  forall es (MP : macro_parameters) params,
  Forall (fun e => ~ ExprHasSideEffects e) es ->
  MP = StringMapProperties.of_list (combine params es) ->
  (forall k e, StringMap.MapsTo k e MP -> ~ ExprHasSideEffects e).
Admitted. *)


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
  - simpl in *. apply demorgan in H. destruct H.
    apply demorgan. split.
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
  ExprEval S E G F M' ef v S' ->
  ExprEval S E G F M' (CallOrInvocation x es) v S' ->
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
  ExprEval S E G F M' ef v S0' ->
  ExprEval S E G F M' (CallOrInvocation x es) v S0' ->

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
  StmtEval S'' Ef G F' M Skip S''' ->
  ExprEval S''' Ef G F' M mexpr v S'''' ->
  (* Only keep in the store the L-value mappings that were there when
     the function was called; i.e., remove from the store all mappings
     whose L-value is in Ef/Sargs. *)
  NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
  ExprEval S E G F' M (CallOrInvocation y es) v S''''' ->
  NatMap.Equal S0' S'''''.
Proof.
  intros.
  apply side_effect_free_macro_no_side_effects
    with (params:=params) (mexpr:=mexpr) (M:=M) (MP:=MP) (ef:=ef) in H7; try assumption.
  apply side_effect_free_function_no_side_effects with
    (params:=params) (fstmt:=Skip) (fexpr:=mexpr) (ls:=ls) (Sargs:=Sargs) (S':=S')
    (S'':=S'') (S''':=S''') (Ef:=Ef) (S'''':=S'''') (vs:=vs) in H21;
      try assumption; try reflexivity.
  rewrite <- H7. rewrite H21. reflexivity.
Qed.


(* Theorem transform_id_sound : forall S E G F M e v S',
  ExprEval S E G F M e v S' ->
  ExprEval S E G F M e v S'.
Proof.
  intros. induction H.
  - apply E_Num. *)

(* Theorem transform_expr_sound : forall S E G F M e v S' e' v' S'' F',
  TransformExpr M F e F' e' ->
  ExprEval S E G F M e v S' ->
  ExprEval S E G F' M e' v' S'' ->
  (NatMap.Equal S' S'') /\ v = v'.
Proof.
  intros S E G F M e v S' e' v' S'' F' H.
  induction H; intros.
  - inversion H. inversion H0. subst. split; reflexivity.
  - inversion H0. inversion H1. subst. apply IHTransformExpr. assumption. assumption.
  - inversion H. *)




Theorem transform_expr_sound : forall M F e F' e',
  TransformExpr M F e F' e' ->
  (forall S E G v S',
  ExprEval S E G F M e v S' ->
  ExprEval S E G F' M e' v S').
Proof.
  intros M F e F' e' H. induction H.
  - intros. inversion H. inversion H0. subst. auto.
  - intros. inversion H0. subst. apply E_ParenExpr. apply IHTransformExpr. assumption.
  - intros. inversion H0. subst. apply E_UnExpr. apply IHTransformExpr. assumption.
  - intros. inversion H3. subst. apply E_BinExpr with S'0.
    + apply H1. apply IHTransformExpr1. apply H14.
    + apply H2. apply IHTransformExpr2. apply H15.
Qed.



