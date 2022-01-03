Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.
From Cpp2C Require Import EvalRules.


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


(* Definition transform_args
  (transform_function :
    func_definitions -> macro_definitions -> expr ->
    (func_definitions*macro_definitions*expr))
  (cur_e : expr)
  (acc : (func_definitions*macro_definitions*(list expr)))
  : (func_definitions*macro_definitions*(list expr)) :=
    let '(lastF, lastM, lastList) := acc in
      let '(newF, newM, newe) :=
        (transform_function lastF lastM cur_e) in
          (newF, newM, newe::lastList).
 *)


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
    match definition x F with
    | Some def => F
    | None =>
      match invocation x M with
      | None => F
      | Some mexpr =>
        match existsb has_side_effects nil with
        | false =>
          match has_side_effects mexpr with
          | false =>
            match get_dynamic_vars mexpr with
            (* Don't recursively transform macro bodies *)
            | nil => ((x ++ "__as_function")%string, (Skip, mexpr))::F
            | dyn_vars => F (* FIXME *)
            end
          | true =>
            match get_dynamic_vars mexpr with
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
    match definition x F with
    (* Where should we call transform_macros_s to transform the
       statements in function bodies? *)
    | Some def => e
    | None =>
      match invocation x M with
      | None => e
      | Some mexpr =>
        match existsb has_side_effects nil with
        | false =>
          match has_side_effects mexpr with
          | false =>
            match get_dynamic_vars mexpr with
            (* Don't recursively transform macro bodies *)
            | nil => CallOrInvocation (x ++ "__as_function") es
            | dyn_vars => e (* FIXME *)
            end
          | true =>
            match get_dynamic_vars mexpr with
            | nil => e (* FIXME *)
            | dyn_vars => e (* FIXME *)
            end
          end
        | true => e
        end
      end
    end
  end.


Check fold_left.

(* Transforms the function definitions list of an expression whose
   CPP usage is being converted to C. *)
Fixpoint transform_macros_F_s
  (F: func_definitions) (M: macro_definitions) (s: stmt) :
  (func_definitions) :=
  match s with
  | Skip => F
  | ExprStmt e => transform_macros_F_e F M e
  | CompoundStmt stmts =>
    fold_left
    (fun (prev_F : func_definitions) (cur_s : stmt) =>
      transform_macros_F_s prev_F M cur_s)
    stmts F
  | IfStmt cond s0 =>
    transform_macros_F_s (transform_macros_F_e F M cond) M s0
  | IfElseStmt cond s0 s1 =>
    transform_macros_F_s
      (transform_macros_F_s (transform_macros_F_e F M cond) M s0)
      M s1
  | WhileStmt cond s0 =>
    transform_macros_F_s (transform_macros_F_e F M cond) M s0
  end.


(* Transforms the macro definitions list of a statement whose
   CPP usage is being converted to C. Currently we don't
   actually alter this. *)
Definition transform_macros_M_s
  (F: func_definitions) (M: macro_definitions) (s: stmt) :
  (macro_definitions) := M.


(* Transforms a statement whose CPP usage is being converted to C. *)
Fixpoint transform_macros_s
  (F: func_definitions) (M: macro_definitions) (s: stmt) :
  (stmt) :=
  match s with
  (* I don't think this isn't entirely right...
     For instance, for IfStmt, should we transform s0 using the
     original F, or the updated F from transforming cond? *)
  | Skip => Skip
  | ExprStmt e => ExprStmt (transform_macros_e F M e)
  | CompoundStmt stmts =>
    CompoundStmt (map (transform_macros_s F M) stmts)
  | IfStmt cond s0 =>
    IfStmt (transform_macros_e F M cond) (transform_macros_s F M s0)
  | IfElseStmt cond s0 s1 =>
    IfElseStmt (transform_macros_e F M cond)
      (transform_macros_s F M s0) (transform_macros_s F M s1)
  | WhileStmt cond s0 =>
    WhileStmt (transform_macros_e F M cond) (transform_macros_s F M s0)
  end.


(* ID transformation - this transformation basically does nothing *)
Fixpoint transform_id_e (e: expr) : expr :=
  match e with
  | Num z => Num z
  | X x => X x
  | ParenExpr e0 => ParenExpr (transform_id_e e0)
  | UnExpr uo e0 => UnExpr uo (transform_id_e e0)
  | BinExpr bo e1 e2 => BinExpr bo (transform_id_e e1) (transform_id_e e2)
  | Assign x e0 => Assign x (transform_id_e e0)
  | CallOrInvocation x es => CallOrInvocation x (map transform_id_e es)
  end.

(* ID transformation - this transformation basically does nothing *)
Fixpoint transform_id_s (s: stmt) : stmt :=
  match s with
  | Skip => Skip
  | ExprStmt e => ExprStmt (transform_id_e e)
  | CompoundStmt stmts => CompoundStmt (map transform_id_s stmts)
  | IfStmt cond s0 =>
    IfStmt (transform_id_e cond) (transform_id_s s0)
  | IfElseStmt cond s0 s1 =>
    IfElseStmt (transform_id_e cond)
      (transform_id_s s0) (transform_id_s s1)
  | WhileStmt cond s0 =>
    WhileStmt (transform_id_e cond) (transform_id_s s0)
  end.
