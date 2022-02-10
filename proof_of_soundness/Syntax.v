(*  Syntax.v
    Defininition of the language syntax.
*)

Require Import
  Coq.Strings.String
  Coq.ZArith.ZArith.


(*  Unary operators *)
Inductive unop : Type :=
  | Positive
  | Negative.


(*  Converts a unop type to its corresponding unary operation *)
Definition unop_to_op (uo : unop) : (Z -> Z) :=
  match uo with
  | Positive => id
  | Negative => Z.opp
  end.


(*  Binary operators *)
Inductive binop : Type :=
  | Plus
  | Sub
  | Mul
  | Div.


(*  Converts a binop type to its corresponding binary operation *)
Definition binop_to_op (bo : binop) : (Z -> Z -> Z) :=
  match bo with
  | Plus => Zplus
  | Sub => Zminus
  | Mul => Zmult
  | Div => Z.div
  end.


(* TODO: Currently we can only assign from strings to R-values.
   This need to be fixed so that LHS of assignments can be an L-value *)
(*  This would necessitate an evaluation rule for L-values as well *)
Inductive expr : Type :=
  | Num (z : Z)
  | Var (x : string)
  | ParenExpr (e0 : expr)
  | UnExpr (uo : unop) (e0 : expr)
  | BinExpr (bo : binop) (e1 e2 : expr)
  | Assign (x: string) (e0 : expr)
  | CallOrInvocation (x : string) (es : list expr).


(*  Statements one would expect to find in an
    imperative programming language *)
Inductive stmt : Type :=
  | Skip
  | Expr (e0 : expr)
  | IfElse (cond : expr) (s1 : stmt) (s2 : stmt)
  | While (cond : expr) (s0 : stmt)
  | Compound (ss : list stmt).

