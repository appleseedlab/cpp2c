Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

(* Unary operators *)
Inductive unop : Type :=
  | Positive
  | Negative.

(* Converts a unop type to its corresponding unary operation *)
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

(* Converts a binop type to its corresponding binary operation *)
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

(* TODO: Add arguments to calls and invocations*)
(* TODO: Currently we can only assign from strings to R-values.
   This need to be fixed so that LHS of assignments can be an L-value *)
Inductive expr : Type :=
  | Num (z : Z)
  | X (x : string)
  | ParenExpr (e0 : expr)
  | UnExpr (uo : unop) (e0 : expr)
  | BinExpr (bo : binop) (e1 e2 : expr)
  | Assign (x: string) (e0 : expr)
  | CallOrInvocation (x : string).

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
