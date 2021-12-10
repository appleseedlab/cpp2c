Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

Open Scope Z_scope.
Open Scope string_scope.


(* I'm not sure if this is correct, but it seems to work *)
Definition environment : Set := list (string * nat).
Definition state : Set := list (nat * Z).

(* TODO: Make these meaningful *)
Definition lookupE (x:string) (E:environment) : nat := 1.
Definition lookupS (l:nat) (S:state) : Z := 1.


Inductive unop : Type :=
  | Positive
  | Negative.

Inductive binop : Type :=
  | Plus
  | Sub
  | Mul
  | Div.

Inductive const_expr : Type :=
  | ConstNum (z : Z)
  | ConstParenExpr (ce : const_expr)
  | ConstUnExpr (uo : unop) (ce : const_expr)
  | ConstBinExpr (bo : binop) (ce1 ce2 : const_expr).

(* TODO: Currently we can only assign from strings to r-values.
   This need to be fixed so that LHS of assignments can be an l-value *)
Inductive expr : Type :=
  | X (x : string)
  | Num (z : Z)
  | ParenExpr (e : expr)
  | UnExpr (uo : unop) (e : expr)
  | BinExpr (bo : binop) (e1 e2 : expr)
  | Assign (x: string) (e : expr)
  | CallOrInvoke (x : string) (es: list expr).

(* TODO: Add state to these evaluation rules.
   May have to define evaluation as a relation instead of as
   a function *)
Fixpoint ceeval (ce : const_expr) : Z :=
  match ce with
  | ConstNum z => z
  | ConstParenExpr ce => ceeval ce
  | ConstUnExpr uo ce =>
    let v := ceeval ce in
      match uo with
     | Positive => id v
     | Negative => - v
     end
  | ConstBinExpr bo ce1 ce2 =>
    let v1 := (ceeval ce1) in
    let v2 := (ceeval ce2) in
      match bo with
      | Plus => v1 + v2
      | Sub => v1 - v2
      | Mul => v1 * v2
      | Div => v1 / v2
      end
end.

Fixpoint eeval (e : expr) : Z :=
  match e with
  | X x => 0
  | Num n => n
  | ParenExpr e => eeval e
  | UnExpr uo e =>
    let v := eeval e in
      match uo with
      | Positive => id v
      | Negative => - v
      end
  | BinExpr bo e1 e2 =>
    let v1 := eeval e1 in
    let v2 := eeval e2 in
      match bo with
      | Plus => v1 + v2
      | Sub => v1 - v2
      | Mul => v1 * v2
      | Div => v1 / v2
      end
  | Assign x e => 
    (* TODO: Return the update to the state! *)
    eeval e
  | CallOrInvoke x vas =>
    (* TODO: Add semantics for function calls and invocations*)
    0
  end.

Reserved Notation
  "[ S , E '|-' e '=>' v , S' ]"
  (at level 90, left associativity).
Inductive eevalR : state -> environment -> expr -> Z -> state -> Prop :=
  (* Variable lookup returns the variable's r-value
     and does not change the state *)
  | E_X : forall S E x l v,
    lookupE x E = l ->
    lookupS l S = v ->
    [S, E |- (X x) => v, S]
  (* Numerals evaluate to their integer representation and do not
     change the state *)
  | E_Num : forall S E n,
    [S, E |- (Num n) => n, S]
  (* Parenthesized expressions evaluate to themselves.
     Currently they do not change the state, but TODO: fix this *)
  | E_ParenExpr : forall S E e v S',
    [S, E |- e => v, S'] ->
    [S, E |- (ParenExpr e) => v, S']
  (* Unary negation evaluates the inner expression, and returns
     the negation of that result along with any side-effects
     from evaluating it*)
  | E_UnExprNegate : forall S E S' e v,
    [S, E |- e => v, S'] ->
    [S', E |- (UnExpr Negative e) => -v, S']
  (* Unary positive evaluates the inner expression, and returns
     the that result along with any side-effects from evaluating it*)
  | E_UnExprPositive : forall S E S' e v,
    [S, E |- e => v, S'] ->
    [S', E |- (UnExpr Positive e) => v, S']
  (* Binary expressions evaluate their inner expressions
     in left-to-right-order, apply their operator to these subresults,
     and return the appropriate result along with any side-effects
     that occurred from evaluating subexpressions. *)
  (* NOTE: Evaluation rules do not handle operator precedence.
     The parser must use a concrete syntax to generate a parse tree
     with the appropriate precedence levels in it.*)
  | E_BinExprPlus : forall S E S' S'' S''' e1 e2 v1 v2,
    [S, E |- e1 => v1, S'] ->
    [S', E |- e2 => v2, S''] ->
    [S'', E |- (BinExpr Plus e1 e2) => (v1 + v2), S''']
  | E_BinExprSub : forall S E S' S'' S''' e1 e2 v1 v2,
    [S, E |- e1 => v1, S'] ->
    [S', E |- e2 => v2, S''] ->
    [S'', E |- (BinExpr Sub e1 e2) => (v1 - v2), S''']
  | E_BinExprMul : forall S E S' S'' S''' e1 e2 v1 v2,
    [S, E |- e1 => v1, S'] ->
    [S', E |- e2 => v2, S''] ->
    [S'', E |- (BinExpr Mul e1 e2) => (v1 * v2), S''']
  | E_BinExprDiv : forall S E S' S'' S''' e1 e2 v1 v2,
    [S, E |- e1 => v1, S'] ->
    [S', E |- e2 => v2, S''] ->
    [S'', E |- (BinExpr Div e1 e2) => (v1 / v2), S''']
  | E_Assign : forall S E l x e v S' S'',
    [S, E |- e => v, S'] ->
    lookupE x E = l ->
    (* TODO: Actually store the variable *)
    (* update S' l v = S''*)
    S'' = S' ->
    [S, E |- (Assign x e) => v, S'']
  where "[ S , E '|-' e '=>' v , S' ]" := (eevalR S E e v S') : type_scope.

Lemma nnzeq : forall z : Z,
  - - z = z.
Proof. induction z as []; reflexivity. Qed.

(* Proof that negation is involute in our language; i.e.,
that applying the unary operation negate to a constant exprression twice
results in the same value.*)
Theorem neg_neg_equal_ce : forall ce : const_expr,
  ceeval (ConstUnExpr Negative (ConstUnExpr Negative ce)) = ceeval ce.
Proof.
  induction ce as []; simpl; rewrite nnzeq; reflexivity.
Qed.

(* Proof that adding zero any constant exprression results in the same
value *)
Theorem optimize_ce: forall ce : const_expr,
  ceeval (ConstBinExpr Plus (ConstNum 0) ce) = ceeval ce.
Proof.
  induction ce as []; reflexivity.
Qed.


(* Define evaluation as a relation instead of a function *)
Inductive cevalR : const_expr -> Z -> Prop :=
  | E_ConstNum (z : Z) : cevalR (ConstNum z) z.


Inductive stmt : Type :=
  (* We may not need this, I added it to make the evaluation rule
     for compound statements easier to define *)
  | Skip
  | ExprStmt (e : expr)
  (* TODO: Add compound statemetns *)
  (* TODO: Allow for ifs without else branches *)
  | IfElseStmt (cond: expr) (s0 s1: stmt)
  | WhileStmt (cond : expr) (s0 : stmt).


Reserved Notation
  "st '=[' s ']=>' st'"
  (at level 91, left associativity).
(* Define the evaluation rule for statements as a
   relation instead of an inductive type to permite the non-
   determinism introduced by while loops *)
Inductive stmtevalR : state -> stmt -> state -> Prop :=
  (* A skip statement does not change the state *)
  | E_Skip : forall st,
    st =[ Skip ]=> st
  (* An expr statement does not change the state (for now) *)
  | E_ExprStmt : forall st e,
    st =[ ExprStmt e ]=> st
  (* An if statement whose expression evaluates to
     has their else statement evaluated *)
  | E_IfElseFalse : forall st st' e s0 s1,
    eeval e = 0 ->
    st =[ s1 ]=> st' ->
    st =[ IfElseStmt e s0 s1 ]=> st'
  (* An if statement whose expression evaluates a nonzero value
     has their true statement evaluated *)
  | E_IfElseTrue : forall st st' e s0 s1,
    eeval e <> 0 ->
    st =[ s0 ]=> st' ->
    st =[ IfElseStmt e s0 s1 ]=> st'
  (* A while statement whose expression evaluates to 0
     does not change the state *)
  | E_WhileFalse : forall st e s0,
    eeval e = 0 ->
    st =[ WhileStmt e s0 ]=> st
  (* This is the interesting one.
     A while statement whose expression evaluates to a nonzero value
     has their body evaluated, then they themselves are evaluated
     again with the updated state *)
  | E_WhileTrue : forall st st' st'' e s0,
    eeval e <> 0 ->
    st =[ s0 ]=> st' ->
    st' =[ WhileStmt e s0 ]=> st'' ->
    st =[ WhileStmt e s0 ]=> st''
  where "st '=[' s ']=>' st'" := (stmtevalR st s st') : type_scope.
