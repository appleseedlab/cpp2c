Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.
From Cpp2C Require Import EvalRules.


(* TODO? We need a function "unify" the results of transformation
   when transforming the F of expressions that contain nested
   expressions / statements. Here's an informal description:
   Input:  F1 and F2, the Fs to unify. It is assumed that all
           functions in these two Fs are uniquely defined.
   Output: Two things: F3, an F containing all the definitions in
           F1 and F2, in which functions with the same body have
           been deduplicated; and a mapping of the type
           string * (list string) in which names of the functions
           in F3 are mapped to names of functions in F2 that have
           the same definition as them.
   Steps:
           1) Create a new F, F3, and a string * (list string)
              mapping Fr.
           2) Add all the functions in F1 into F3, and all
              the function names in F1 to the domain of Fr.
           3) For each function in F2, check if a function with
              the same body exists in F3. If false, then add the
              function from F2. If true, then add the name of the
              F2 function to the list of names that the F3 function
              name is mapped to in Fr.
           4) Return F3 and Fr.
  The reason we return Fr is so that after unifying the Fs, we can
  traverse the AST and replace calls to functions from F2 for which
  an identically-defined function in F3 exists with a call to the
  identical function.
*)

(*
(* TODO *)
Definition unify_Fs
  (F1 : func_definitions)
  (F2 : func_definitions) :
  (func_definitions * (list (string * list string)) ) :=
  let F3 := F1 in
    let Fr := map  F3 in
        fold_left
          (fun pair : (func_definitions * list (string * list string)
               fdef : func_definition =>
            if find same_func_def F
          F2 (F3, Fr)
where get_fname (fun pair : (string * func_definition) =>
      (fst pair, nil)):= 
*)


(* Clang has a function for doing this, though it is conservative *)
(* Returns true if an expression has side-effects, false otherwise *)
Definition has_side_effects (e : expr) : bool.
Admitted.

(* Returns the list of dynamic variables used within
   a macro definition *)
(* TODO: Fix this to actually work. It will probably need the caller
   environment added to its parameter list.
   This will in turn necessitate adding the caller environment to
   transform function below, since that is where this function is
   used *)
Definition get_dynamic_vars (md : macro_definition) : list string.
Admitted.


(* Transforms the function definitions list of an expression whose
   CPP usage is being converted to C. *)
Fixpoint transform_macros_F_e
  (F: func_definitions) (M: macro_definitions) (e : expr) :
  (func_definitions) :=
  match e with
  | Num z => F
  | X x => F
  | ParenExpr e0 => transform_macros_F_e F M e0
  | UnExpr uo e0 => transform_macros_F_e F M e0
  | BinExpr bo e1 e2 =>
    (* Here's a potential issue: How to handle recursive
       transformations in expressions with more than one operand?
       This is currently causing a problem in the soundness proof.
       I think the best solution would be to transform F using e2, and
       feed the result into the function definition list transformation
       using e2. This would be the same as doing a left fold of the
       F transformation function over a list of two expressions.
       Is that sound though; and if so, how to prove that it is? *)
    let F' := transform_macros_F_e F M e1 in
      transform_macros_F_e F' M e2
    (* app (transform_macros_F F M e1) (transform_macros_F F M e2) *)
  | Assign x e0 => transform_macros_F_e F M e0
  | CallOrInvocation x es =>
    match definition F x with
    (* Do we transform macros that do macro shadowing?
       Or do we leave them as-is? This currently does the latter. *)
    | Some def => F
    | None =>
      match invocation M x with
      | None => F
      | Some (params, mexpr) =>
        match existsb has_side_effects nil with
        | false =>
          match has_side_effects mexpr with
          | false =>
            match get_dynamic_vars (params, mexpr) with
            (* Don't recursively transform macro bodies *)
            | nil => ((x ++ "__as_function")%string, (params, Skip, mexpr))::F
            | dyn_vars => F (* FIXME *)
            end
          | true =>
            match get_dynamic_vars (params, mexpr) with
            | nil => F (* FIXME *)
            | dyn_vars => F (* FIXME *)
            end
          end
        | true => F
        end
      end
    end
  end.


(* Transforms the macro definitions list of an expression whose
   CPP usage is being converted to C. Currently we don't
   actually alter this. *)
Definition transform_macros_M_e
  (F: func_definitions) (M: macro_definitions) (e: expr) :
  (macro_definitions) := M.


(* Transforms an expression whose CPP usage is being converted to C.
   Not all transformations are supported yet. *)
Fixpoint transform_macros_e
  (F: func_definitions) (M: macro_definitions) (e: expr) :
  (expr) :=
  match e with
  | Num z => e
  | X x => e
  | ParenExpr e0 => ParenExpr (transform_macros_e F M e0)
  | UnExpr uo e0 => UnExpr uo (transform_macros_e F M e0)
  | BinExpr bo e1 e2 =>
    (* Again: How to handle this? Currently this is not
      technically correct, since we should be feeding the transformed
      F from the first operand to the transformation for the second
      operand. Or is this correct, and we should perform both operands'
      transformations using the original F? *)
    BinExpr bo (transform_macros_e F M e1) (transform_macros_e F M e2)
  | Assign x e0 => Assign x (transform_macros_e F M e0)
  | CallOrInvocation x es =>
    match definition F x with
    (* Where should we call transform_macros_s to transform the
       statements in function bodies? *)
    (* Do we transform macros that do macro shadowing?
       Or do we leave them as-is? This currently does the latter. *)
    | Some def => e
    | None =>
      match invocation M x with
      | None => e
      | Some (params, mexpr) =>
        match existsb has_side_effects nil with
        | false =>
          match has_side_effects mexpr with
          | false =>
            match get_dynamic_vars (params, mexpr) with
            (* Don't recursively transform macro bodies *)
            | nil => CallOrInvocation (x ++ "__as_function") es
            | dyn_vars => e (* FIXME *)
            end
          | true =>
            match get_dynamic_vars (params, mexpr) with
            | nil => e (* FIXME *)
            | dyn_vars => e (* FIXME *)
            end
          end
        | true => e
        end
      end
    end
  end.


(* Transforms the function definitions list of an expression whose
   CPP usage is being converted to C. *)
Fixpoint transform_macros_F_s
  (F: func_definitions) (M: macro_definitions) (s: stmt) :
  (func_definitions) :=
  match s with
  (* Nothing changes *)
  | Skip => F
  (* Transform the inner expression's function list *)
  | ExprStmt e => transform_macros_F_e F M e
  (* Transform each inner statements' F and unify results *)
  | CompoundStmt stmts =>
    fold_left
    (fun (prev_F : func_definitions) (cur_s : stmt) =>
      transform_macros_F_s prev_F M cur_s)
    stmts F
  (* Transform the condition and true branch's F and unify results *)
  | IfStmt cond s0 =>
    transform_macros_F_s (transform_macros_F_e F M cond) M s0
  (* Transform the condition and branchs' F and unify results *)
  | IfElseStmt cond s0 s1 =>
    transform_macros_F_s
      (transform_macros_F_s (transform_macros_F_e F M cond) M s0)
      M s1
  (* Transform the condition and inner statement's F and
     unify results *)
  | WhileStmt cond s0 =>
    transform_macros_F_s (transform_macros_F_e F M cond) M s0
  end.


(* Transforms the macro definitions list of a statement whose
   CPP usage is being converted to C. Currently we don't
   actually alter this. *)
Definition transform_macros_M_s
  (F: func_definitions) (M: macro_definitions) (s: stmt) :
  (macro_definitions) := M.


(* Transforms a statement whose CPP usage is being converted to C *)
Fixpoint transform_macros_s
  (F: func_definitions) (M: macro_definitions) (s: stmt) :
  (stmt) :=
  match s with
  (* Nothing changes *)
  | Skip => Skip
  (* Transform the inner expression *)
  | ExprStmt e => ExprStmt (transform_macros_e F M e)
  (* Transform each inner statement *)
  | CompoundStmt stmts =>
    CompoundStmt (map (transform_macros_s F M) stmts)
  (* Transform the condition and true branch *)
  | IfStmt cond s0 =>
    IfStmt (transform_macros_e F M cond) (transform_macros_s F M s0)
  (* Transform the condition and branches *)
  | IfElseStmt cond s0 s1 =>
    IfElseStmt (transform_macros_e F M cond)
      (transform_macros_s F M s0) (transform_macros_s F M s1)
  (* Transform the condition and inner statement *)
  | WhileStmt cond s0 =>
    WhileStmt (transform_macros_e F M cond) (transform_macros_s F M s0)
  end.
