Require Import
  Coq.FSets.FMapFacts
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  Coq.Structures.OrderedTypeEx
  Coq.Structures.OrdersEx
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  Syntax.

(* Mappings from natural numbers to a type *)
Module Import NatMap := FMapList.Make(OrderedTypeEx.Nat_as_OT).
Module NatMapProperties := WProperties_fun OrderedTypeEx.Nat_as_OT NatMap.
Module NatMapFacts := NatMapProperties.F.

(* Mappings from strings to a type *)
Module Import StringMap := FMapList.Make(String_as_OT).
Module StringMapProperties := WProperties_fun String_as_OT StringMap.
Module StringMapFacts := StringMapProperties.F.

(* Store is a mapping from l-values (memory addresses, represented as
   natural numbers) to r-values (just integers in our case) *)
Definition store : Type := NatMap.t Z.

(* Environment is a mapping from symbols (strings) to l-values (memory
   addresses; see above) *)
Definition environment : Type := StringMap.t nat.

(* A function is defined by a 3-tuple containing its parameters (strings),
   body (a statement, which may be a compound statement), and
   return expression *)
Definition function_definition : Set := ((list string) * stmt * expr).

(* A function table is a mapping from function names (strings) to
   function definitions *)
Definition function_table : Type := StringMap.t function_definition.

(* A macro is defined by a 2-tuple containing its parameters (strings),
   and body (for now simply an expression *)
Definition macro_definition : Set := ((list string) * expr).

(* A macro table is a mapping from macro names (strings) to
   macro definitions *)
Definition macro_table : Type := StringMap.t macro_definition.

(* A macro parameters is a mapping from macro parameters (strings) to
   expressions *)
(* Definition macro_parameters : Type := StringMap.t expr. *)

(* Macro parameters are defined this way to facilitate the proof.
   Originally we defined them as a StringMap mapping to expressions,
   but the problem with this is that it was difficult (maybe impossible?)
   to prove that if the mappings was created from a set of keys ks combined
   with a set of elements es, and a predicate holds for all the elements of es
   originally, then it will hold for any elemnt that a key maps to in
   the mapping. Unfortunately, Coq's FMap built-in lemmas aren't quite strong
   enough to prove this, but its List lemmas are strong enough to prove a
   similar lemma for associative arrays. Maybe in the future we can find an
   external library that proves this for us; that would be ideal.
*)
Definition macro_parameters : Set := list (string * expr).
Definition lookup_macro_parameter
  (MP : macro_parameters) (k : string) : option (string * expr) :=
  List.find (fun pe => String.eqb (fst pe) k) MP.
Fixpoint remove_macro_parameter
  (l : macro_parameters) (k : string) : macro_parameters :=
  match l with
  | nil => nil
  | cons x xs => if String.eqb (fst x) k then
    remove_macro_parameter xs k else x :: (remove_macro_parameter xs k)
  end.



(* Coq map examples *)

(* Compute StringMap.find "x"%string (StringMap.empty nat). *)

Example no_mappings_in_empty_map : ~ MapsTo "x"%string 1 (empty nat).
Proof.
  intros. assert (Empty (empty nat)). apply is_empty_2. reflexivity.
  apply H.
Qed.

(* Compute NatMapProperties.update (NatMap.empty nat) (NatMap.empty nat). *)

Example no_mappings_in_empty_joined_map : forall x,
~ NatMap.MapsTo x 1 (NatMapProperties.update (NatMap.empty nat) (NatMap.empty nat)).
Proof.
  intros. unfold not. intros. apply NatMapProperties.update_mapsto_iff in H.
  destruct H.
  - apply NatMapFacts.empty_mapsto_iff in H. apply H.
  - destruct H. apply NatMapFacts.empty_mapsto_iff in H. apply H.
Qed.

