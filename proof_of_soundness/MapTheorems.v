Require Import
  Coq.FSets.FMapList
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  ConfigVars.



Lemma NatMap_eq_Equal : forall (t : Type) (m : NatMap.t t) m',
  m = m' ->
  NatMap.Equal m m'.
Proof.
  intros. subst. reflexivity.
Qed.


Lemma StringMap_eq_Equal : forall (t : Type) (m : StringMap.t t) m',
  m = m' ->
  StringMap.Equal m m'.
Proof.
  intros. subst. reflexivity.
Qed.


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


Theorem StringMap_disjoint_diff_Equal : forall (S1 : function_table) (S2 : function_table),
  StringMapProperties.Disjoint S1 S2 ->
  StringMap.Equal S1 (StringMapProperties.diff (StringMapProperties.update S1 S2) S2).
Proof.
  intros. apply StringMapFacts.Equal_mapsto_iff. intros. split.
  - intros. apply StringMapProperties.diff_mapsto_iff. split.
    + apply StringMapProperties.update_mapsto_iff. right. split.
      * assumption.
      * unfold StringMapProperties.Disjoint in H.
        apply StringMap_mapsto_in in H0. unfold not. intros. unfold not in H.
        apply H with k. split.
        -- assumption.
        -- assumption.
    + unfold StringMapProperties.Disjoint in H.
      apply StringMap_mapsto_in in H0. unfold not. intros. unfold not in H.
      apply H with k. split.
      * assumption.
      * assumption.
  - intros. apply StringMapProperties.diff_mapsto_iff in H0. destruct H0.
    apply StringMapProperties.update_mapsto_iff in H0. destruct H0.
    * apply StringMap_mapsto_in in H0. contradiction.
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