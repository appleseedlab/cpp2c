Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

Open Scope Z_scope.
Open Scope string_scope.


(* I'm not sure if this is correct, but it seems to work *)
Definition state : Set := list (string * Z).


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
  | ConstBinExpr (ce1 ce2 : const_expr) (bo : binop).

Inductive var_expr : Type :=
  | X (x : string)
  | Num (z : Z)
  | ParenExpr (va : var_expr)
  | UnExpr (uo : unop) (va : var_expr)
  | BinExpr (va1 va2 : var_expr) (bo : binop)
  | Assign (va1 va2 : var_expr)
  | CallOrInvoke (x : string) (vas: list var_expr).

Inductive expr : Type :=
  | ConstExpr (ce : const_expr)
  | VarExpr (va : var_expr).

(* TODO: Make this meaningful*)
Definition lookup (x:string) : Z := 1.

(* TODO: Add state to these evaluation rules.
   May have to define evaluation as a relation instead of as
   a function *)
Fixpoint ceval (ce : const_expr) : Z :=
  match ce with
  | ConstNum z => z
  | ConstParenExpr ce => ceval ce
  | ConstUnExpr uo ce =>
    let v := ceval ce in
      match uo with
     | Positive => id v
     | Negative => - v
     end
  | ConstBinExpr ce1 ce2 bo =>
    let v1 := (ceval ce1) in
    let v2 := (ceval ce2) in
      match bo with
      | Plus => v1 + v2
      | Sub => v1 - v2
      | Mul => v1 * v2
      | Div => v1 / v2
      end
end.


Fixpoint veval (va : var_expr) : Z :=
  match va with
  | X x => lookup x
  | Num n => n
  | ParenExpr va => veval va
  | UnExpr uo va =>
    let v := veval va in
      match uo with
      | Positive => id v
      | Negative => - v
      end
  | BinExpr va1 va2 bo =>
    let v1 := veval va1 in
    let v2 := veval va2 in
      match bo with
      | Plus => v1 + v2
      | Sub => v1 - v2
      | Mul => v1 * v2
      | Div => v1 / v2
      end
  | Assign va1 va2 => 
    (* TODO: Return the update to the state! *)
    veval va2
  | CallOrInvoke x vas =>
    (* TODO: Add semantics for function calls and invocations*)
    0
  end.


Definition eeval (e : expr) : Z :=
  match e with
  | ConstExpr ce => ceval ce
  | VarExpr va => veval va
  end.

Lemma nnzeq : forall z : Z,
  - - z = z.
Proof. induction z as []; reflexivity. Qed.

(* Proof that negation is involute in our language; i.e.,
that applying the unary operation negate to a constant exprression twice
results in the same value.*)
Theorem neg_neg_equal_ce : forall ce : const_expr,
  ceval (ConstUnExpr Negative (ConstUnExpr Negative ce)) = ceval ce.
Proof.
  induction ce as []; simpl; rewrite nnzeq; reflexivity.
Qed.

(* Proof that adding zero any constant exprression results in the same
value *)
Theorem optimize_ce: forall ce : const_expr,
  ceval (ConstBinExpr (ConstNum 0) ce Plus) = ceval ce.
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
  (at level 90, left associativity).
(* Define the evaluation rule for statements as a
   relation instead of an inductive type to permite the non-
   determinism introduced by while loops *)
Inductive stmtevalR : stmt -> state -> state -> Prop :=
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
  where "st '=[' s ']=>' st'" := (stmtevalR s st st') : type_scope.
