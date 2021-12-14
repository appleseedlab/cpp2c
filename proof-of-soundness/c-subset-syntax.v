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
  match find (fun pair => String.eqb (fst pair) x) E with
  | None => None
  | Some (_, l) => Some l
  end.

(* Looks up an L-value in the store and returns
   the corresponding R-value wrapped in an option type if found;
   otherwise returns None *)
Definition lookupS (l:nat) (S:state) : option Z :=
  match find (fun pair => Nat.eqb (fst pair) l) S with
  | None => None
  | Some (_, z) => Some z
  end.

(* Compute (find (fun s => s =? "s") (nil)). *)
(* Compute (find (fun s => s =? "s") (cons "s" (nil))). *)

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
  | FunctionCall (x : string) (es: list expr)
  | MacroInvocation (x : string) (es: list expr).

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
(* Functions are defined as a 4-tuple:
   0: List of parameter names
   1: List of declarations
   2: List of statements
   3: Return expressions
*)
(* This is actually kind of ugly, because it says that a function
   definition could be a list of declarations, which could each
   either be global or local. Since they are inside a function body,
   however, of course they are local. How to rectify this? *)
Definition func_definition : Set :=
  ((list string) * (list decl) * (list stmt) * expr).
Definition func_definitions : Set := @list (string * func_definition).

(* Macro definitions are serialized as a two-tuple containing a
   list of their parameter names and their macro body
   (a single expression) *)
Definition macro_body : Set := ((list string) * expr).
Definition macro_bodies : Set := @list (string * macro_body).

(* Looks up a function name in the function defintion list and returns
   the corresponding definition wrapped in an option type if found;
   otherwise returns None *)
Definition definition
  (x:string) (defs:func_definitions) : option func_definition :=
  match find (fun pair => String.eqb (fst pair) x) defs with
  | None => None
  | Some (_, def) => Some def
  end.

(* Looks up a macro name in the function defintion list and returns
   the corresponding definition wrapped in an option type if found;
   otherwise returns None *)
Definition invocation
  (x:string) (defs:macro_bodies) : option macro_body :=
  match find (fun pair => String.eqb (fst pair) x) defs with
  | None => None
  | Some (_, body) => Some body
  end.

(* Right now, a term that fails to evaluate will simply get "stuck";
   we do not provide any error messages. I think we could add this
   later using a sum type. *)
Reserved Notation
  "[ S , E , F , M '|-' e '=>' v , S' ]"
  (at level 90, left associativity).

Inductive eevalR :
  state -> environment -> func_definitions -> macro_bodies ->
  expr -> Z ->
  state -> Prop :=
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
  (* TODO *)
  | E_FunctionCall: forall S E F M x es def,
    definition x F = Some def ->
    [S, E, F, M |- (FunctionCall x es) => 0, S]
  (* Macro invocation, no side-effects *)
  (* TODO *)
  | E_MacroInvocationNoSideEffects : forall S E F M x es body,
    invocation x M = Some body ->
    [S, E, F, M |- (MacroInvocation x es) => 0, S]
  where "[ S , E , F , M '|-' e '=>' v , S' ]" := (eevalR S E F M e v S') : type_scope.

(* TODO: Fix evaluation rules for statements *)

Open Scope Z_scope.

Reserved Notation
  "[ S , E , F , M '=[' s ']=>' S' ]"
  (at level 91, left associativity).
(* Define the evaluation rule for statements as a
   relation instead of an inductive type to permite the non-
   determinism introduced by while loops *)
Inductive stmtevalR :
  state -> environment -> func_definitions -> macro_bodies ->
  stmt ->
  state -> Prop :=
  (* A skip statement does not change the state *)
  | E_Skip : forall S E F M,
    [S, E, F, M =[ Skip ]=> S]
  (* An expression statement evaluates its expression and returns 
     the resulting state *)
  | E_ExprStmt : forall S E F M e v S',
    eevalR S E F M e v S' ->
    [S, E, F, M =[ ExprStmt e ]=> S']
  (* An empty compound statement evaluates to its initial state *)
  | E_CompoundStatementEmpty : forall S E F M,
    [S, E, F, M =[ CompoundStmt nil ]=> S]
  | E_CompoundStatementNotEmpty : forall S  E F M stmts s0 rst S' S'',
    head stmts = Some s0 ->
    tail stmts = rst ->
    [S, E, F, M =[ s0 ]=> S'] ->
    [S', E, F, M =[ CompoundStmt rst ]=> S''] ->
    [S', E, F, M =[ CompoundStmt stmts ]=> S'']
  (* TODO: If statement *)
  (* TODO: If else statement *)
  (* TODO: While statement *)
  
  where "[ S , E , F , M '=[' s ']=>' S' ]" := (stmtevalR S E F M s S') : type_scope.

Close Scope Z_scope.


Close Scope string_scope.
