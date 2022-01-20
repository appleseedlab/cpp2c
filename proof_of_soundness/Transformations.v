Require Import
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  EvalRules.



Inductive TransformExpr :
  macro_table -> function_table -> expr ->
  function_table -> expr -> Prop :=
  | Transform_Num : forall M F z,
    TransformExpr M F (Num z) F (Num z)
  | Transform_ParenExpr : forall M F e0 F' e0',
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (ParenExpr e0) F' (ParenExpr e0')
  | Transform_UnExpr : forall M F e0 F' e0' uo,
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (UnExpr uo e0) F' (UnExpr uo e0')
  | Transform_BinExpr : forall M F e1 e2 F' F'' F''' e1' e2' bo,
    TransformExpr M F e1 F' e1' ->
    TransformExpr M F e2 F'' e2' ->
    
    (* Note that we don't explicity create F''' here. In the implementation, F''' will
       be created as the the unification of F' and F''. *)
    (* We need these extra theorems until we resolve the unique names problem, but
       these should make sense for now*)
    (* If we can evaluate the left expression under its F transformation, then we can
       evaluate it under the unified F list *)
    (forall S E G v S',
      ExprEval S E G F' M e1' v S' -> ExprEval S E G F''' M e1' v S') ->
    (* Similarly, if we can evaluate the right expression under its F transformation,
       then we can evaluate it under the unified F list as well *)
    (forall S'0 E G v2 S',
      ExprEval S'0 E G F'' M e2' v2 S' -> ExprEval S'0 E G F''' M e2' v2 S') ->
    TransformExpr M F (BinExpr bo e1 e2) F''' (BinExpr bo e1' e2').








(* macro_table -> function_table -> expr ->
function_table -> expr



Prove:
StringMap.MapsTo new_name definition (add new_name definition F) ->


    | TransformMacrosNoSideEffects
    Forall (fun e => ~ ExprHasSideEffects e) es ->
    ~ ExprHasSideEffects mexpr ->
    ~ StringMap.In new_name M ->
    ~ StringMap.In new_name F ->
    F' = StringMap.add new_name definition F ->
    Transform M F (CallOrInvocation x es) F' (CallOrInvocation new_name es)

forall S E G F M e v S' S'' v F' e',
  H: Transform M F e F' e' ->
  H0: ExprEval S E G F M e v S' ->
  H1: ExprEval S E G F' M e' v' S'' ->
  H2: StringMap.Equal S' S'' /\ v = v'

induction H.
  - apply E_MacroInvocation in H0.
    apply E_FunctionCall in H1. *)

















(* We need a function "unify" the results of transformation
   when transforming the F of expressions that contain nested
   expressions / statements. Here's an informal description:
   Input:  F1 and F2, the Fs to unify. It is assumed that all
           functions in these two Fs are uniquely defined.
   Output: Two things: F3, an F containing all the definitions in
           F1 and F2, in which functions with the same body have
           been deduplicated; and a mapping of strings to lists
           of strings in which names of the functions
           in F3 are mapped to names of functions in F2 that have
           the same definition as them.
   Steps:
           1) Create a new F, F3, and a string to list of string
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
  We shouldn't implement this in Coq but we will need this when
  we go to implement the actual transformation tool.
*)
(* 

(* Returns the list of variables within a macro expression
   that are referenced from the caller environment *)
Fixpoint get_vars_in_caller_environment
  (E: environment)
  (e: expr) : list string :=
  match e with
  | Num z => nil
  | X x => match lookupE E x with
    | None => nil
    | Some _ => x::nil
    end
  | ParenExpr e0 => get_vars_in_caller_environment E e0
  | UnExpr uo e0 => get_vars_in_caller_environment E e0
  | BinExpr bo e1 e2 =>
    (get_vars_in_caller_environment E e1) ++
    (get_vars_in_caller_environment E e2)
  | Assign x e0 => match lookupE E x with
    | None => (get_vars_in_caller_environment E e0)
    | Some _ => x::(get_vars_in_caller_environment E e0)
    end
  | CallOrInvocation x es =>
    let dyn_es := flat_map (get_vars_in_caller_environment E) es in
    match lookupE E x with
    | None => dyn_es
    | Some _ => x::dyn_es
    end
end.



(* Transforms the function definitions list of an expression whose
   CPP usage is being converted to C. *)
Fixpoint transform_macros_F_e
  (F: func_definitions)
  (M: macro_definitions)
  (E: environment)
  (e: expr) :
  (func_definitions) :=
  match e with
  | Num z => F
  | X x => F
  | ParenExpr e0 => transform_macros_F_e F M E e0
  | UnExpr uo e0 => transform_macros_F_e F M E e0
  | BinExpr bo e1 e2 =>
    (* Here's a potential issue: How to handle recursive
       transformations in expressions with more than one operand?
       This is currently causing a problem in the soundness proof.
       I think the best solution would be to transform F using e2, and
       feed the result into the function definition list transformation
       using e2. This would be the same as doing a left fold of the
       F transformation function over a list of two expressions.
       Is that sound though; and if so, how to prove that it is? *)
    let F' := transform_macros_F_e F M E e1 in
      transform_macros_F_e F' M E e2
    (* app (transform_macros_F F M e1) (transform_macros_F F M e2) *)
  | Assign x e0 => transform_macros_F_e F M E e0
  | CallOrInvocation x es =>
    match definition F x with
    (* Do we transform macros that do macro shadowing?
       Or do we leave them as-is? This currently does the latter. *)
    | Some def => F
    | None =>
      match invocation M x with
      | None => F
      | Some (params, mexpr) =>
        match existsb expr_has_side_effects es with
        | false =>
          match expr_has_side_effects mexpr with
          | false =>
            match get_vars_in_caller_environment E mexpr with
            (* Don't recursively transform macro bodies *)
            | nil => ((x ++ "__as_function")%string, (params, Skip, mexpr))::F
            | dyn_vars => F (* FIXME *)
            end
          | true =>
            match get_vars_in_caller_environment E mexpr with
            | nil => F (* FIXME *)
            | dyn_vars => F (* FIXME *)
            end
          end
        | true => F
        end
      end
    end
  end.


(* Transforms an expression whose CPP usage is being converted to C.
   Not all transformations are supported yet. *)
Fixpoint transform_macros_e
  (F: func_definitions)
  (M: macro_definitions)
  (E: environment)
  (e: expr) :
  (expr) :=
  match e with
  | Num z => e
  | X x => e
  | ParenExpr e0 => ParenExpr (transform_macros_e F M E e0)
  | UnExpr uo e0 => UnExpr uo (transform_macros_e F M E e0)
  | BinExpr bo e1 e2 =>
    (* Again: How to handle this? Currently this is not
      technically correct, since we should be feeding the transformed
      F from the first operand to the transformation for the second
      operand. Or is this correct, and we should perform both operands'
      transformations using the original F? *)
    BinExpr bo (transform_macros_e F M E e1) (transform_macros_e F M E e2)
  | Assign x e0 => Assign x (transform_macros_e F M E e0)
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
        match existsb expr_has_side_effects es with
        | false =>
          match expr_has_side_effects mexpr with
          | false =>
            match get_vars_in_caller_environment E mexpr with
            (* Don't recursively transform macro bodies *)
            | nil => CallOrInvocation (x ++ "__as_function") es
            | dyn_vars => e (* FIXME *)
            end
          | true =>
            match get_vars_in_caller_environment E mexpr with
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
  (F: func_definitions)
  (M: macro_definitions)
  (E: environment)
  (s: stmt) :
  (func_definitions) :=
  match s with
  (* Nothing changes *)
  | Skip => F
  (* Transform the inner expression's function list *)
  | ExprStmt e => transform_macros_F_e F M E e
  (* Transform each inner statements' F and unify results *)
  | CompoundStmt stmts =>
    fold_left
    (fun (prev_F : func_definitions) (cur_s : stmt) =>
      transform_macros_F_s prev_F M E cur_s)
    stmts F
  (* Transform the condition and true branch's F and unify results *)
  | IfStmt cond s0 =>
    transform_macros_F_s (transform_macros_F_e F M E cond) M E s0
  (* Transform the condition and branchs' F and unify results *)
  | IfElseStmt cond s0 s1 =>
    transform_macros_F_s
      (transform_macros_F_s (transform_macros_F_e F M E cond) M E s0)
      M E s1
  (* Transform the condition and inner statement's F and
     unify results *)
  | WhileStmt cond s0 =>
    transform_macros_F_s (transform_macros_F_e F M E cond) M E s0
  end.


(* Transforms a statement whose CPP usage is being converted to C *)
Fixpoint transform_macros_s
  (F: func_definitions)
  (M: macro_definitions)
  (E: environment)
  (s: stmt) :
  (stmt) :=
  match s with
  (* Nothing changes *)
  | Skip => Skip
  (* Transform the inner expression *)
  | ExprStmt e => ExprStmt (transform_macros_e F M E e)
  (* Transform each inner statement *)
  | CompoundStmt stmts =>
    CompoundStmt (map (transform_macros_s F M E)stmts)
  (* Transform the condition and true branch *)
  | IfStmt cond s0 =>
    IfStmt (transform_macros_e F M E cond) (transform_macros_s F M E s0)
  (* Transform the condition and branches *)
  | IfElseStmt cond s0 s1 =>
    IfElseStmt (transform_macros_e F M E cond)
      (transform_macros_s F M E s0) (transform_macros_s F M E s1)
  (* Transform the condition and inner statement *)
  | WhileStmt cond s0 =>
    WhileStmt (transform_macros_e F M E cond) (transform_macros_s F M E s0)
  end.
 *)