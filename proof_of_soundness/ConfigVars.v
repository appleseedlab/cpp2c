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
Definition macro_parameters : Type := StringMap.t expr.

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

