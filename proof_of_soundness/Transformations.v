Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.
From Cpp2C Require Import EvalRules.

Open Scope string_scope.

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


Fixpoint transform_macros
  (F: func_definitions) (M: macro_definitions) (e:expr) :
  (func_definitions * macro_definitions * expr) :=
  match e with
  (* Don't transform a numeral *)
  | Num z => (F, M, Num z)
  (* Don't transform a variable *)
  | X x => (F, M, X x)
  (* Transform the inner expression of a parenthesized expression *)
  | ParenExpr e =>
    let '(F', M', e') := (transform_macros F M e) in
      (F', M', ParenExpr e')
  (* Transform the operand of a unary expression *)
  | UnExpr uo e => 
    let '(F', M', e') := (transform_macros F M e) in
      (F', M', UnExpr uo e')
  (* Transform the operands of a binary expression *)
  | BinExpr bo e1 e2 =>
    let '(F', M', e1') := transform_macros F M e1 in
      let '(F'', M'', e2') := (transform_macros F' M' e2) in
        (F'', M'', BinExpr bo e1' e2')
  (* Transform the expression of an assignment *)
  (* (this will have to change if L-value evaluation is added *)
  | Assign x e =>
    let '(F', M', e') := (transform_macros F M e) in
      (F', M', Assign x e')
  (* Transformation here varies whether a function or macro invocation
     is being called *)
  | CallOrInvocation x =>
    match definition x F with
    (* If this identifier maps to a function definition,
       then don't transform it *)
    | Some def => (F, M, CallOrInvocation x)
    | None =>
      (* Otherwise it may be a macro, and the transformation will
         depend upon other conditions *)
      match invocation x M with
      | Some mexpr =>
        (* add guard clauses for different transformations *)
        (* need a way of generating a fresh name *)
        (* Do any of the the macro arguments have side_effects? *)
        match existsb has_side_effects nil with
        (* If not, then proceed with other checks *)
        | false =>
          (* Does the macro body have side-effects? *)
          match has_side_effects mexpr with
          | false =>
            (* Does the macro use dynamic scoping? *)
            match get_dynamic_vars mexpr with
            (* No, so just transform the macro to a function *)
            | nil =>
              (* Don't remove from M; copy a new definition
                 to just F *)
              let fname := x ++ "__as_function" in
                (* And recursively transform the invocation arguments *)
                let F' := (fname, (Skip, mexpr))::F in
                  (F', M, CallOrInvocation fname)
            (* Yes, so add the dynamic variables to the transformed
             function's parameter list *)
            | dyn_vars => (F, M, e) (* FIXME *)
            end
          | true =>
            (* Does the macro use dynamic scoping? *)
            match get_dynamic_vars mexpr with
            (* No, so just transform the macro to a function *)
            | nil => (F, M, e) (* FIXME *)
            (* Yes, so add the dynamic variables to the transformed
               function's parameter list *)
            | dyn_vars => (F, M, e) (* FIXME *)
            end
          end
        (* If so, then don't transform the macro *)
        | true => (F, M, e)
        end
      (* If a call can't be connected to a function or macro, then
         it's erroneous anyway so leave it as-is *)
      | None => (F, M, e)
      end
    end
  end.


(* Transforms macros into functions, using the fixpoint evaluation function *)
Fixpoint transform_macros_eval
  (i : nat)
  (S: state) (E: environment)
  (F: func_definitions) (M: macro_definitions)
  (e : expr) : option (Z*state) :=
  match i with
  | O => None
  | S i' =>
    match e with
    | Num z => expreval i S E F M (Num z)
    | X x => expreval i S E F M (X x)
    | ParenExpr e0 => transform_macros_eval i' S E F M e0
    | UnExpr uo e0 =>
      match transform_macros_eval i' S E F M e0 with
      | None => None
      | Some (v', S') => Some ((unopToOp uo) v', S')
      end
    | BinExpr bo e1 e2 =>
      match transform_macros_eval i' S E F M e1 with
      | None => None
      | Some (v1, S') =>
        match transform_macros_eval i' S' E F M e2 with
        | None => None
        | Some (v2, S'') => Some ((binopToOp bo) v1 v2, S'')
        end
      end
    | Assign x e0 =>
      match transform_macros_eval i' S E F M e0 with
      | None => None
      | Some (v, S') =>
        match lookupE x E with
        | None => None
        | Some l =>
          match lookupS l S with
          | None => None
          | Some _ => Some (v, (l, v)::S')
          end
        end
      end
    | CallOrInvocation x =>
      match definition x F with
      | None =>
        match invocation x M with
        | None => None
        | Some mexpr =>
          transform_macros_eval i' S E ((x, (Skip, mexpr))::F) M (CallOrInvocation x)
        end
      | Some (fstmt, fexpr) =>
        match stmteval i' S E F M fstmt with
        | None => None
        | Some S' => transform_macros_eval i' S' E F M fexpr
        end
      end
    end
  end.


(* ID transformation - this transformation basically does nothing *)
Fixpoint transform_id
  (e:expr) : expr :=
  match e with
  | Num z => Num z
  | X x => X x
  | ParenExpr e0 => ParenExpr (transform_id e0)
  | UnExpr uo e0 => UnExpr uo (transform_id e0)
  | BinExpr bo e1 e2 => BinExpr bo (transform_id e1) (transform_id e2)
  | Assign x e0 => Assign x (transform_id e0)
  | CallOrInvocation x => CallOrInvocation x
  end.

Close Scope string_scope.
