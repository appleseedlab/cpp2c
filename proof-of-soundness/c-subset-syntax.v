Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

Open Scope string_scope.

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

(* Unary operators *)
Inductive unop : Type :=
  | Positive
  | Negative.

Definition unopToOp (uo : unop) : (Z -> Z) :=
  match uo with
  | Positive => id
  | Negative => Z.opp
  end.

(* Binary operators *)
Inductive binop : Type :=
  | Plus
  | Sub
  | Mul
  | Div.

Definition binopToOp (bo : binop) : (Z -> Z -> Z) :=
  match bo with
  | Plus => Zplus
  | Sub => Zminus
  | Mul => Zmult
  | Div => Z.div
  end.

(* Syntax for constant expressions, i.e., ones that don't involve
   variables and don't have side-effects *)
Inductive const_expr : Type :=
  | ConstNum (z : Z)
  | ConstParenExpr (ce : const_expr)
  | ConstUnExpr (uo : unop) (ce : const_expr)
  | ConstBinExpr (bo : binop) (ce1 ce2 : const_expr).

(* TODO: Currently we can only assign from strings to R-values.
   This need to be fixed so that LHS of assignments can be an L-value *)
Inductive expr : Type :=
  | X (x : string)
  | Num (z : Z)
  | ParenExpr (e : expr)
  | UnExpr (uo : unop) (e : expr)
  | BinExpr (bo : binop) (e1 e2 : expr)
  | Assign (x: string) (e : expr)
  | CallOrInvocation (x : string) (es: list expr).

Inductive stmt : Type :=
  (* We may not need this, I added it to make the evaluation rule
     for compound statements easier to define *)
  | Skip
  | ExprStmt (e : expr)
  | CompoundStmt (stmts: list stmt)
  | IfStmt (cond: expr) (s0 : stmt)
  | IfElseStmt (cond: expr) (s0 s1: stmt)
  | WhileStmt (cond: expr) (s0 : stmt).

(* Maybe these should be split up into two separate types?
   See the definition of func_definition for an explanation why *)
Inductive decl : Type :=
  | LocalDecl (x:string) (e:expr)
  | GlobalDecl (x:string) (ce:const_expr).

(* Mappings from function and macro names to their definitions *)
(* Functions are defined as a 3-tuple:
   0: Environment which contains processed local declarations and
      parameters
   1: Body that is a statement (could be a compound statement)
   2: Return expression *)
(* TODO: Eventually we may want to swap the environment out for a
         parameter list and operate on that instead *)
Definition func_definition : Set :=
  (environment * stmt * expr).
Definition func_definitions : Set := @list (string * func_definition).

(* Macro definitions are serialized as a two-tuple containing
   the macros parameters mapped to their arguments (the environment)
   and the macro body (a single expression).
   TODO: This does not exactly model how macros work. To fix this,
         we will need to swap out the environment for a list of
         parameters and the body for something more akin to what we
         have for functions.
   *)
Definition macro_definition : Set := (environment * expr).
Definition macro_definitions : Set := @list (string * macro_definition).

(* Looks up a function name in the function defintion list and returns
   the corresponding definition wrapped in an option type if found;
   otherwise returns None *)
Definition definition
  (x:string) (defs:func_definitions) : option func_definition :=
  option_map snd (find (fun pair => String.eqb (fst pair) x) defs).

(* Looks up a macro name in the function defintion list and returns
   the corresponding definition wrapped in an option type if found;
   otherwise returns None *)
Definition invocation
  (x:string) (defs:macro_definitions) : option macro_definition :=
  option_map snd (find (fun pair => String.eqb (fst pair) x) defs).

(* Right now, a term that fails to evaluate will simply get "stuck";
   i.e. it will fail to be reduced further.
   We do not provide any error messages, but I think we could add this
   later using a sum type. *)
(* TODO: Add G, the global environment *)

Open Scope Z_scope.

Reserved Notation
  "[ S , E , F , M '|-' e '=>' v , S' ]"
  (at level 90, left associativity).
Reserved Notation
  "{ S , E , F , M '=[' s ']=>' S' }"
  (at level 91, left associativity).
Inductive exprevalR :
  state -> environment -> func_definitions -> macro_definitions ->
  expr ->
  Z -> state -> Prop :=
  (* Variable lookup returns the variable's R-value
     and does not change the state *)
  | E_X_Success : forall S E F M x l v,
    lookupE x E = Some l ->
    lookupS l S = Some v ->
    [S, E, F, M |- (X x) => v, S]
  (* Numerals evaluate to their integer representation and do not
     change the state *)
  | E_Num : forall S E F M n,
    [S, E, F, M |- (Num n) => n, S]
  (* Parenthesized expressions evaluate to themselves *)
  | E_ParenExpr : forall S E F M e v S',
    [S, E, F, M |- e => v, S'] ->
    [S, E, F, M |- (ParenExpr e) => v, S']
  (* Unary expressions *)
  | E_UnExpr : forall S E F M S' uo e v,
    [S, E, F, M |- e => v, S'] ->
    [S', E, F, M |- (UnExpr uo e) => ((unopToOp uo) v), S']
  (* Binary expressions *)
  (* NOTE: Evaluation rules do not handle operator precedence.
     The parser must use a concrete syntax to generate a parse tree
     with the appropriate precedence levels in it. *)
  | E_BinExpr : forall S E F M bo e1 e2 S' v1 S'' v2 S''',
    [S, E, F, M |- e1 => v1, S'] ->
    [S', E, F, M |- e2 => v2, S''] ->
    [S'', E, F, M |- (BinExpr bo e1 e2) => (((binopToOp bo) v1 v2)), S''']
  | E_Assign_No_Identifier: forall S E F M x e v S',
    [S, E, F, M |- e => v, S'] ->
    lookupE x E = None ->
    [S, E, F, M |- (Assign x e) => v, S]
  (* Variable assignments update the store by adding a new L-value to
     R-value mapping or by overriding an existing one.
     The R-value is returned along with the updated state *)
  | E_Assign_Success : forall S E F M l x e v S',
    [S, E, F, M |- e => v, S'] ->
    lookupE x E = Some l ->
    [S, E, F, M |- (Assign x e) => v, (l,v)::S']
  (* For function calls, each of the function call's arguments are
     evaluated, then the function call itself is evaluated, and finally
     the result of the call is returned along with the ultimate state. *)
  | E_FunctionCall: forall S E F M x es fenv fstmt fexpr S' v S'',
    definition x F = Some (fenv, fstmt, fexpr) ->
    {S, fenv, F, M =[ fstmt ]=> S'} ->
    [S, fenv, F, M |- fexpr => v, S''] ->
    [S, E, F, M |- (CallOrInvocation x es) => v, S'']
  (* Macro invocation*)
  (* FIXME *)
  | E_MacroInvocation : forall S E F M x es menv mexpr v S',
    invocation x M = Some (menv, mexpr) ->
    [S, menv, F, M |- mexpr => v, S'] ->
    [S, E, F, M |- (CallOrInvocation x es) => v, S']
  where "[ S , E , F , M '|-' e '=>' v , S' ]" := (exprevalR S E F M e v S')
(* Define the evaluation rule for statements as a
   relation instead of an inductive type to permite the non-
   determinism introduced by while loops *)
with stmtevalR :
  state -> environment -> func_definitions -> macro_definitions ->
  stmt ->
  state -> Prop :=
  (* A skip statement does not change the state *)
  | E_Skip : forall S E F M,
    {S, E, F, M =[ Skip ]=> S}
  (* An expression statement evaluates its expression and returns 
     the resulting state *)
  | E_ExprStmt : forall S E F M e v S',
    exprevalR S E F M e v S' ->
    {S, E, F, M =[ ExprStmt e ]=> S'}
  (* An empty compound statement evaluates to its initial state *)
  | E_CompoundStatementEmpty : forall S E F M,
    {S, E, F, M =[ CompoundStmt nil ]=> S}
  (* A non-empty compound statement evaluates its first statement and
     then the following statements *)
  | E_CompoundStatementNotEmpty : forall S E F M stmts s0 rst S' S'',
    head stmts = Some s0 ->
    tail stmts = rst ->
    {S, E, F, M =[ s0 ]=> S'} ->
    {S', E, F, M =[ CompoundStmt rst ]=> S''} ->
    {S, E, F, M =[ CompoundStmt stmts ]=> S''}
  (* An if statement whose condition evaluates to false only carries
     over the side-effects induced by evaluating its condition *)
  | E_IfFalse: forall S E F M e s0 S',
    [S, E, F, M |- e => 0, S'] ->
    {S, E, F, M =[ IfStmt e s0 ]=> S'}
  (* An if statement whose condition evaluates to true carries over
     the side-effects from evaluating its condition and its statement *)
  | E_IfTrue: forall S E F M e s0 v S' S'',
    v <> 0 ->
    [S, E, F, M |- e => v, S'] ->
    {S',E, F, M =[ s0 ]=> S''} ->
    {S, E, F, M =[ IfStmt e s0 ]=> S''}
  (* Side-effects from condition and false branch *)
  | E_IfElseFalse: forall S E F M e s0 s1 S' S'',
    [S, E, F, M |- e => 0, S'] ->
    {S',E, F, M =[ s1 ]=> S''} ->
    {S, E, F, M =[ IfElseStmt e s0 s1 ]=> S''}
  (* Side-effects from condition and true branch *)
  | E_IfElseTrue: forall S E F M e s0 s1 v S' S'',
    v <> 0 ->
    [S, E, F, M |- e => v, S'] ->
    {S',E, F, M =[ s0 ]=> S''} ->
    {S, E, F, M =[ IfElseStmt e s0 s1 ]=> S''}
  (* Similar to E_IfFalse *)
  | E_WhileFalse: forall S E F M e s0 S',
    [S, E, F, M |- e => 0, S'] ->
    {S, E, F, M =[ WhileStmt e s0 ]=> S'}
  (* A while statement whose condition evaluates to false must be run
     again after evaluating its body *)
  | E_WhileTrue: forall S E F M e s0 v S' S'' S''',
    v <> 0 ->
    [S, E, F, M |- e => v, S'] ->
    {S', E, F, M =[ s0 ]=> S''} ->
    {S'', E, F, M =[ WhileStmt e s0 ]=> S'''} ->
    {S, E, F, M =[ WhileStmt e s0 ]=> S'''}
  where "{ S , E , F , M '=[' s ']=>' S' }" := (stmtevalR S E F M s S').

Close Scope Z_scope.

(* Returns true if an expression has side-effects, false otherwise *)
Definition has_side_effects (e : expr) : bool. Admitted.

(* Returns the list of dynamic variables used within
   a macro definition *)
(* TODO: Fix this to actually work. It will probably need the caller
   environment added to its parameter list.
   This will in turn necessitate adding the caller environment to
   transform function below, since that is where this function is
   used *)
Definition get_dynamic_vars (md : macro_definition) : list string.
Admitted.

Fixpoint transform
  (F: func_definitions) (M: macro_definitions) (e:expr) : 
  (func_definitions * macro_definitions * expr) :=
  match e with
 (* Don't transform variables *)
 | X x => (F, M, X x)
 (* Don't transform numerals *)
 | Num z => (F, M, Num z)
 (* Transform the inner expression of a parenthesize expression *)
 | ParenExpr e =>
    let '(F', M', e') := (transform F M e) in
      (F', M', ParenExpr e')
 (* Transform the operand of a unary expressions *)
 | UnExpr uo e => 
    let '(F', M', e') := (transform F M e) in
      (F', M', UnExpr uo e')
 (* Transform the operands of a binary expressions *)
 | BinExpr bo e1 e2 =>
    let '(F', M', e1') := transform F M e1 in
      let '(F'', M'', e2') := (transform F' M' e2) in
         (F'', M'', BinExpr bo e1' e2')
 (* Transform the expression of an assignment *)
 (* (this will have to change if L-value evaluation is added *)
 | Assign x e =>
    let '(F', M', e') := (transform F M e) in
      (F', M', Assign x e')
 (* Transformation here varies whether a function or macro invocation
    is being called *)
 | CallOrInvocation x es =>
    match definition x F with
    (* If this identifier maps to a function definition, then the
       original piece of code was a function call.
       We don't transform functions, but since each of the function
       call arguments are expressions, we have to iterate over and
       transform each of them.
       We implement this iteration via a right fold to avoid
       having to reverse the list afterward. *)
    | Some def =>
      let '(finalF, finalM, finalList) :=
      fold_right (
        fun e acc =>
          let '(lastF, lastM, lastList) := acc in
            let '(newF, newM, newe) := (transform lastF lastM e) in
              (newF, newM, newe::lastList)
        ) (F, M, nil) es in
          (finalF, finalM, CallOrInvocation x finalList)
    | None =>
        match invocation x M with
        | Some (menv, mexpr) =>
          (* add guard clauses for different transformations *)
          (* need a way of generating a fresh name *)
          (* Do any of the the macro arguments have side_effects? *)
          match existsb has_side_effects es with
            (* If not, then proceed with other checks *)
            | false =>
              (* Does the macro body have side-effects? *)
              match has_side_effects mexpr with
              | false =>
                (* Does the macro use dynamic scoping? *)
                match get_dynamic_vars (menv, mexpr) with
                (* No, so just transform the macro to a function *)
                | nil =>
                  (* Don't remove from M; copy a new definition
                     to just F *)
                  let fname := x ++ "__as_function" in
                    let F' := (fname, (menv, Skip, mexpr))::F in
                      (F', M, CallOrInvocation fname es)
                (* Yes, so add the dynamic variables to the transformed
                   function's parameter list *)
                | dyn_vars => (F, M, e) (* FIXME *)
                end
              | true =>
                (* Does the macro use dynamic scoping? *)
                match get_dynamic_vars (menv, mexpr) with
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


(* Variables are equivalent under transformation *)
Fact var_eq_transformed :
  forall (S S': state) (E : environment)
         (F F': func_definitions) (M M': macro_definitions)
         (e e': expr) (x : string) (v : Z),
  e = X x ->
  transform F M e = (F', M', e') ->
  exprevalR S E F M e v S' = exprevalR S E F' M' e' v S'.
Proof.
  intros.
  rewrite H in H0. simpl in H0. rewrite <- H in H0.
  inversion H0.
  reflexivity.
Qed.

(* Numerals are equivalent under transformation *)
Theorem num_eq_transformed : 
  forall (S S': state) (E : environment)
         (F F': func_definitions) (M M': macro_definitions)
         (e e': expr) (v z: Z),
  e = Num z ->
  transform F M e = (F', M', e') ->
  exprevalR S E F M e v S' = exprevalR S E F' M' e' v S'.
Proof.
  intros.
  rewrite H in H0. simpl in H0. rewrite <- H in H0.
  inversion H0.
  reflexivity.
Qed.

(* A parenthesized expression whose inner expression is equivalent
   under transformation is also equivalent under transformation *)
Theorem paren_expr_eq_transformed : 
  forall (S S' S'': state) (E : environment)
         (F F0' F': func_definitions) (M M0' M': macro_definitions)
         (e innerExpr innerExpr' e': expr) (v: Z),
  e = ParenExpr innerExpr ->
  transform F M innerExpr = (F0', M0', innerExpr') ->
  (F, M, innerExpr) = (F0', M0', innerExpr') ->
  exprevalR S E F M innerExpr v S' = exprevalR S E F0' M0' innerExpr' v S' ->
  transform F0' M0' e = (F', M', e') ->
  exprevalR S' E F M e v S'' = exprevalR S' E F' M' e' v S''.
Proof.
  intros.
  inversion H1.
  rewrite H in H3. simpl in H3.
  rewrite <- H5 in H3. rewrite <- H6 in H3. rewrite H0 in H3.
  inversion H3. rewrite <- H7. rewrite <- H. reflexivity.
Qed.

(* A call to a macro without side-effects is equivalent to a call
   to the transformed version of that macro as a function *)
Theorem func_call_eq_transformed_macro_no_side_effects : 
  forall (S S': state) (E menv : environment)
         (F F': func_definitions) (M M': macro_definitions)
         (e mexpr e': expr) (x fname : string) (es : list expr)
         (v : Z),
  e = CallOrInvocation x es ->
  definition x F = None ->
  invocation x M = Some (menv, mexpr) ->
  existsb has_side_effects es = false ->
  has_side_effects mexpr = false ->
  get_dynamic_vars (menv, mexpr) = nil ->
  fname = x ++ "__as_function" ->
  transform F M e = (F', M', e') ->
  definition fname F = Some (menv, Skip, mexpr) ->
  (* This premise is VERY strong, can we weaken it?
     Here we assume that a call to the macro will result
     in the same value and state as a call to the
     transformed function will. *)
  exprevalR S E F M (CallOrInvocation x es) v S' =
  exprevalR S E F' M' (CallOrInvocation fname es) v S' ->
  exprevalR S E F M e v S' = exprevalR S E F' M' e' v S'.
Proof.
  intros.
  rewrite H in H6. simpl in H6.
  rewrite H0, H1, H2, H3, H4 in H6.
  rewrite <- H5 in H6.
  inversion H6.
  simpl. rewrite H. pattern M' at 1; rewrite <- H11. rewrite H10.
  rewrite H8. reflexivity.
Qed.


Close Scope string_scope.
