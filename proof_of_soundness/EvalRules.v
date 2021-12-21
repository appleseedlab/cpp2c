Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.

Section EvalRules.

Open Scope Z_scope.

(* Here is an attempt to define evaluation using a function.
   This does not work because evaluation is inherently
   nondeterministic, but could work if we added a "step"
   variable to force evaluation to eventually terminate *)
Fixpoint expreval
  (i : nat)
  (S : state) (E : environment)
  (F : func_definitions) (M : macro_definitions)
  (e : expr) : option (Z * state) :=
  match i with
  | O => None
  | S i' =>
    match e with
    | Num z => Some (z, S)
    | X x =>
      match lookupE x E with
      | None => None
      | Some l =>
        match lookupS l S with
        | None => None
        | Some v => Some (v, S)
        end
      end
    | ParenExpr e0 => expreval i' S E F M e0
    | UnExpr uo e0 =>
      match expreval i' S E F M e0 with
      | None => None
      | Some (v, S') => Some((unopToOp uo) v, S')
      end
    | BinExpr bo e1 e2 =>
      match expreval i' S E F M e1 with
      | None => None
      | Some (v1, S') =>
        match expreval i' S' E F M e2 with
        | None => None
        | Some (v2, S'') => Some ((binopToOp bo) v1 v2, S'')
        end
      end
    | Assign x e0 =>
      match expreval i' S E F M e0 with
      | None => None
      | Some (v, S') =>
        match lookupE x E with
        | None => None
        | Some l =>
          match lookupS l S' with
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
          expreval i' S E F M mexpr
        end
      | Some (fstmt, fexpr) =>
        match stmteval i' S E F M fstmt with
        | None => None
        | Some S' =>
          expreval i' S' E F M fexpr
        end
      end
    end
  end
with stmteval
  (i : nat)
  (S : state) (E : environment)
  (F : func_definitions) (M : macro_definitions)
  (s : stmt) : option state :=
  match i with
  | O => None
  | S i' =>
    match s with
    | Skip => Some S
    | ExprStmt e =>
      match expreval i' S E F M e with
      | None => None
      | Some (_, S') => Some S'
      end
    | CompoundStmt stmts =>
      match stmts with
      | nil => Some S
      | cons s0 rst =>
        match stmteval i' S E F M s0 with
        | None => None
        | Some S' =>
          match stmteval i' S' E F M (CompoundStmt rst) with
          | None => None
          | Some S'' => Some S''
          end
        end
      end
    | IfStmt cond s0 =>
      match expreval i' S E F M cond with
      | None => None
      | Some (0, S') => Some S'
      | Some (_, S') => stmteval i' S' E F M s0
      end
    | IfElseStmt cond s0 s1 =>
      match expreval i' S E F M cond with
      | None => None
      | Some (0, S') => stmteval i' S' E F M s0
      | Some (_, S') => stmteval i' S' E F M s1
      end
    | WhileStmt cond s0 =>
      match expreval i' S E F M cond with
      | None => None
      | Some (0, S') => Some S'
      | Some (_, S') => stmteval i' S' E F M (WhileStmt cond s0)
      end
    end
  end.


(* Right now, a term that fails to evaluate will simply get "stuck";
   i.e. it will fail to be reduced further.
   We do not provide any error messages, but I think we could add this
   later using a sum type. *)
(* TODO: Add G, the global environment *)
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
  (* Numerals evaluate to their integer representation and do not
     change the state *)
  | E_Num : forall S E F M z,
    [S, E, F, M |- (Num z) => z, S]
  (* Variable lookup returns the variable's R-value
     and does not change the state *)
  | E_X_Success : forall S E F M x l v,
    lookupE x E = Some l ->
    lookupS l S = Some v ->
    [S, E, F, M |- (X x) => v, S]
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
  | E_FunctionCall: forall S E F M x fstmt fexpr S' v S'',
    definition x F = Some (fstmt, fexpr) ->
    {S, E, F, M =[ fstmt ]=> S'} ->
    [S, E, F, M |- fexpr => v, S''] ->
    [S, E, F, M |- (CallOrInvocation x) => v, S'']
  (* Macro invocation*)
  (* FIXME *)
  | E_MacroInvocation : forall S E F M x mexpr v S',
    invocation x M = Some mexpr ->
    [S, E, F, M |- mexpr => v, S'] ->
    [S, E, F, M |- (CallOrInvocation x) => v, S']
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

End EvalRules.