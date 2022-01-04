Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

From Cpp2C Require Import Syntax.

(* Environment and store/state are implemented as associative arrays. *)
Definition environment : Set := @list (string * nat).
Definition state : Set := @list (nat * Z).

(* Looks up a variable name in the environment and returns
   the corresponding L-value wrapped in an option type if found;
   otherwise returns None *)
Definition lookupE (x:string) (E:environment) : option nat :=
  option_map snd (find (fun pair => String.eqb (fst pair) x) E).

(* Looks up an L-value in the store and returns
   the corresponding R-value wrapped in an option type if found;
   otherwise returns None *)
Definition lookupS (l:nat) (S:state) : option Z :=
  option_map snd (find (fun pair => Nat.eqb (fst pair) l) S).


(* Mappings from function and macro names to their definitions *)
(* Functions are defined as a 3-tuple:
   0: Environment which contains processed local declarations and
      parameters
   1: Body that is a statement (could be a compound statement)
   2: Return expression *)
(* TODO: Eventually we may want to swap the environment out for a
         parameter list and operate on that instead *)
Definition func_definition : Set := ((stmt) * expr).
Definition func_definitions : Set := @list (string * func_definition).

(* Macro definitions are serialized as a two-tuple containing
   the macros parameters mapped to their arguments (the environment)
   and the macro body (a single expression).
   TODO: This does not exactly model how macros work. To fix this,
         we will need to swap out the environment for a list of
         parameters and the body for something more akin to what we
         have for functions.
   *)
Definition macro_definition : Set := (expr).
Definition macro_definitions : Set := @list (string * macro_definition).

(* Looks up a function name in the function defintion list and returns
   the corresponding definition wrapped in an option type if found;
   otherwise returns None *)
Definition definition
  (defs:func_definitions) (x:string) : option func_definition :=
  option_map snd (find (fun pair => String.eqb (fst pair) x) defs).

(* Looks up a macro name in the function defintion list and returns
   the corresponding definition wrapped in an option type if found;
   otherwise returns None *)
Definition invocation
  (defs:macro_definitions) (x:string) : option macro_definition :=
  option_map snd (find (fun pair => String.eqb (fst pair) x) defs).
