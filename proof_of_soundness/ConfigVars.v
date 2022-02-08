(*  ConfigVars.v
    Definitions of the configuration variables used to specify
    the operational semantics for the language.
*)

Require Import
  Coq.FSets.FMapFacts
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  Coq.Structures.OrderedTypeEx
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  Syntax.

(* Mappings from natural numbers to a type *)
Module Import NatMap := FMapList.Make(OrderedTypeEx.Nat_as_OT).
Module NatMapProperties := WProperties_fun OrderedTypeEx.Nat_as_OT NatMap.
Module NatMapFacts := NatMapProperties.F.
Module NatMapOP := OrdProperties NatMap.


(* Mappings from strings to a type *)
Module Import StringMap := FMapList.Make(OrderedTypeEx.String_as_OT).
Module StringMapProperties := WProperties_fun OrderedTypeEx.String_as_OT StringMap.
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
