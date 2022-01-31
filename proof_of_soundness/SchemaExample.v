(*  TODO: Read the following
    https://stackoverflow.com/questions/56093251/a-proof-about-a-mutually-inductive-proposition
    https://stackoverflow.com/questions/55196816/induction-principle-for-le
 *)


Require Import List.

Set Implicit Arguments.

Inductive even_length {A : Type} : list A -> Prop:=
| e_nil : even_length nil
| e_cons : forall e l, odd_length l -> even_length (e::l)
with
  odd_length {A : Type} : list A -> Prop :=
  | o_cons : forall e l, even_length l -> odd_length (e::l).


Lemma map_even : forall A B (f : A -> B) (l : list A),
    even_length l -> even_length (map f l).
Proof.
  induction l.
  (** nil *)
  - intros. simpl. constructor.
  (** cons *)
  - intros. simpl.
    inversion H. subst.
    constructor.
    Abort. (** odd_length l -> odd_length (map f l) would help *)


Scheme even_length_mut := Induction for even_length Sort Prop
with odd_length_mut := Induction for odd_length Sort Prop.

Check even_length_mut.

Lemma map_even : forall A B (f : A -> B) (l : list A),
    even_length l -> even_length (map f l).
Proof.
  intros.
  apply (even_length_mut (fun l (h : even_length l) => even_length (map f l) )
                         (fun l (h : odd_length l) => odd_length (map f l) )
        ).
  - simpl. constructor.
  - intros. simpl. constructor. auto.
  - intros. simpl. constructor. auto.
  - auto.
Qed.

Theorem even_list_ind {A} (P : list A -> Prop) :
  P nil ->
  (forall x y l, even_length l -> P l -> P (x :: y :: l)) ->
  forall l, even_length l -> P l.
Proof.
  intros. apply even_length_ind.
  - auto.
  - intros.



Lemma map_odd_even {A B} (f : A -> B) : forall l : list A,
  (even_length l -> even_length (map f l)) /\
  (odd_length l -> odd_length (map f l)).
Proof.
  induction l.
  - split.
    + intros. constructor.
    + intros. inversion H.
  - split.
    + intros. simpl. constructor. apply IHl. inversion H. subst. apply H1.
    + intros. simpl. constructor. inversion H. subst. apply IHl. apply H1.
Qed.