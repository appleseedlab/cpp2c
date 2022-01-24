(* IDEA:
   First practice JUST transforming the F by adding the new function definitions to it.
   It may be better to instead of directly adding new definitions to F, to collect all
   the new definitions into their own map, then update the current map with the map
   of new function in the returned map. This would allow use to add assertions about the two
   maps being disjoint, which would in turn allow us to prove the soundness of function
   lookup. *)

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


Lemma NatMap_Empty_empty : forall (t : Type) (m : NatMap.t t),
  NatMap.Empty (elt:=_) m ->
  NatMap.Equal m (NatMap.empty _).
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


Lemma no_side_effects_no_store_change_eq : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  ExprEval S E G F M e v S' ->
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
    apply demorgan in H.
    rewrite <- IHE1_1 in IHE1_2.
    apply IHE1_2.  apply H. apply H.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
  - unfold ExprHasSideEffects in H. contradiction.
Qed.


Lemma no_side_effects_expreval_expreval : forall e,
  ~ ExprHasSideEffects e ->
  forall S E G F M v S',
  ExprEval S E G F M e v S' ->
  ExprEval S E G F M e v S.
Proof.
  intros e H S E G F M v S' E1.
  induction E1.
  - apply E_Num.
  - apply E_LocalVar with l; assumption.
  - apply E_GlobalVar with l; assumption.
  - apply E_ParenExpr. apply IHE1. assumption.
  - apply E_UnExpr. apply IHE1. assumption.
  - unfold ExprHasSideEffects in H. fold ExprHasSideEffects in H.
    apply demorgan in H. destruct H. apply E_BinExpr with S'.
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
  StmtEval S E G F M Skip S' ->
  NatMap.Equal S S'.
Proof.
  intros. induction H. reflexivity.
Qed.


(* The following lemmas involve all parts of program evaluation
   (e.g., expression, argument list, and statement evaluation).
   Coq's built-in induction tactic is not powerful enough to provide
   us with the induction hypotheses necessary to prove these lemmas, so
   we must define our own induction schema for these proofs *)
Scheme ExprEval_mut := Induction for ExprEval Sort Prop
with StmtEval_mut := Induction for StmtEval Sort Prop
with EvalArgs_mut := Induction for EvalArgs Sort Prop.


Lemma stmteval_notin_F_add_stmteval : forall S E G F M stmt S',
  StmtEval S E G F M stmt S' ->
  forall x fdef,
    ~ StringMap.In x F ->
    StmtEval S E G (StringMap.add x fdef F) M stmt S'.
Proof.
(*
  This proof could be solved instead with the following ltac code:
    intros. induction H; try constructor.
  Instead I have opted to use our custom schema here so that it may serve
  as a simple demonstration of how to use schemas *)
  intros. apply (
    (* First we apply the appropriate schema like a tactic *)
    StmtEval_mut
      (* Then we have to define a custom inductive hypothesis for each Prop
         that the one we are inducting over is mutually inductive with
         (in this case just the StmtEval Prop since statement evaluation
         currently only includes skip statements, which don't
         involve expressions) *)
      (fun S E G F M stmt S' (h : StmtEval S E G F M stmt S') =>
        StmtEval S E G (StringMap.add x fdef F) M stmt S')
  ); try constructor; auto.
Qed.


Lemma expreval_notin_F_add_expreval : forall S E G F M e v S',
  ExprEval S E G F M e v S' ->
  forall x fdef,
    ~ StringMap.In x F ->
    ExprEval S E G (StringMap.add x fdef F) M e v S'.
Proof.
  apply (
    ExprEval_mut
      (* ExprEval *)
      (fun S E G F M e v S' (h : ExprEval S E G F M e v S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        ExprEval S E G (StringMap.add x fdef F) M e v S' )
      (* StmtEval *)
      (fun S E G F M stmt S' (h : StmtEval S E G F M stmt S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        StmtEval S E G (StringMap.add x fdef F) M stmt S' )
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
      params fstmt fexpr ls Sargs S' S'' S''' Ef S'''' vs; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
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
  StmtEval S'' Ef G F M fstmt S''' ->
  ExprEval S''' Ef G F M fexpr v S'''' ->
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
  ExprEval S E G F M (CallOrInvocation x es) v S' ->
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
  ExprEval S E G F M (CallOrInvocation x es) v S0' ->

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
Lemma stmteval_transformargs_stmteval : forall S E G F M stmt S' F' stmt',
  StmtEval S E G F M stmt S' ->
  TransformStmt M F stmt F' stmt' ->
  StmtEval S E G F' M stmt S'.
Proof.
  intros. induction H0. assumption.
Qed.


Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformArgs_mut := Induction for TransformArgs Sort Prop
with TransformStmt_mut := Induction for TransformStmt Sort Prop.



(* Attempt 1: Induction over the transformation with schema *)
Theorem transform_expr_sound : forall M F e F' e',
  TransformExpr M F e F' e' ->
  (* The proof will not work if these variables were introduced sooner.
     Doing so would interfere with the induction hypothesis *)
  forall S E G v S',
    ExprEval S E G F M e v S' ->
    ExprEval S E G F' M e' v S'.
Proof.
  intros M F e F' e' H. apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
    forall S E G v S',
    ExprEval S E G F M e v S' ->
    ExprEval S E G F' M e' v S')
    (* TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
    forall S E G v S',
    ExprEval S E G F M e v S' ->
    ExprEval S E G F' M e' v S')
    (* TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
    forall S E G v S',
    ExprEval S E G F M e v S' ->
    ExprEval S E G F' M e' v S')); auto.
  - intros. inversion_clear H1. apply E_ParenExpr. apply H0; auto.
  - intros. inversion_clear H1. apply E_UnExpr. apply H0; auto.
  - intros. inversion_clear H2. apply E_BinExpr with S'0.
Abort.


(* Attempt 2: Induction over the evaluation *)
Theorem expreval_transform_expreval : forall S E G F M e v S',
  ExprEval S E G F M e v S' ->
  forall F' e',
    TransformExpr M F e F' e' ->
    ExprEval S E G F' M e' v S'.
Proof.
  intros S E G F M e v S' H. induction H; try (intros F' e' H; inversion_clear H; econstructor; auto).
  - intros. inversion_clear H1. apply E_LocalVar with l; auto.
  - intros. inversion_clear H2. apply E_GlobalVar with l; auto.
  - intros. inversion_clear H0. apply E_ParenExpr; auto.
  - intros. inversion_clear H0. apply E_UnExpr; auto.
  - intros. inversion_clear H1. apply E_BinExpr with S'.
    + apply IHExprEval1.
Abort.


(* Attempt 3: Induction over the evaluation with schema *)
Theorem expreval_transform_expreval : forall S E G F M e v S',
  ExprEval S E G F M e v S' ->
  forall F' e',
    TransformExpr M F e F' e' ->
    ExprEval S E G F' M e' v S'.
Proof.
  intros S E G F M e v S' H.
  apply (
    ExprEval_mut
      (* ExprEval *)
      (fun S E G F M e v S' (h : ExprEval S E G F M e v S' ) =>
        forall F' e',
          TransformExpr M F e F' e' ->
          ExprEval S E G F' M e' v S')
      (* StmtEval *)
      (fun S E G F M stmt S' (h : StmtEval S E G F M stmt S' ) =>
        forall F' stmt',
          TransformStmt M F stmt F' stmt' ->
          StmtEval S E G F' M stmt' S')
      (* EvalArgs *)
      (fun Sprev Ecaller G F M es vs Snext (h : EvalArgs Sprev Ecaller G F M es vs Snext) =>
        forall F' es',
          TransformArgs M F es F' es' ->
          EvalArgs Sprev Ecaller G F' M es' vs Snext)
    ); try (intros; econstructor; auto).
  - intros. inversion_clear H0. constructor.
  - intros. inversion_clear H0. apply E_LocalVar with l; auto.
  - intros. inversion_clear H0. apply E_GlobalVar with l; auto.
  - intros. inversion_clear H1. apply E_ParenExpr; auto.
  - intros. inversion_clear H1. apply E_UnExpr; auto.
  - intros. inversion_clear H2. apply E_BinExpr with S'0.
    + apply H5. apply H0. (* apply H3. *) admit.
    + apply H1. apply H4.
  - intros. inversion_clear H1. apply E_Assign_Local with l S'0; auto.
  - intros. inversion_clear H1. apply E_Assign_Global with l S'0; auto.
  - intros. inversion_clear H3.
    + apply H6 with
          params0 fstmt0 fexpr0 params fstmt fexpr in H5. inversion H5. subst.
      apply E_FunctionCall with
        params fstmt' fexpr' ls Sargs S'0 S'' S''' Ef S'''' vs; auto.
      * rewrite H10. apply StringMapFacts.add_mapsto_iff. left. auto.
      * apply H0. admit.
      * apply H1. admit.
      * apply H2. admit.
    + apply StringMap_mapsto_in in H4. contradiction.
  - intros. inversion_clear H1.
    + apply StringMap_mapsto_in in m. contradiction.
    + apply H3 with
        params0 mexpr0 params mexpr in H2. inversion H2. subst.
      apply E_FunctionCall with
        (params:=params) (fstmt:=Skip) (fexpr:=mexpr) (ls:=ls) (Sargs:=Sargs) (S':=S')
        (S'':=S'') (S''':=S''') (Ef:=Ef) (S'''':=S'''') (vs:=vs); auto.
      * rewrite H8. apply StringMapFacts.add_mapsto_iff. left; auto.
      * Abort.