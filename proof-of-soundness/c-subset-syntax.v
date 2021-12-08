Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Open Scope Z_scope.



Inductive unop : Type :=
  | Positive
  | Negative.

Inductive binop : Type :=
  | Plus
  | Sub
  | Mul
  | Div.

Inductive const_exp : Type :=
  | ConstNum (z : Z)
  | ConstParenExpr (ce : const_exp)
  | ConstUnOp (uo : unop) (ce : const_exp)
  | ConstBinOp (ce1 ce2 : const_exp) (bo : binop).

Inductive var_exp : Type :=
  | X (x : string)
  | Num (z : Z)
  | ParenExpr (va : var_exp)
  | UnOp (uo : unop) (va : var_exp)
  | BinOp (va1 va2 : var_exp) (bo : binop)
  | Assign (va1 va2 : var_exp)
  | CallOrInvoke (x : string) (vas: list var_exp).

Inductive exp : Type :=
  | ConstExpr (ce : const_exp)
  | VarExpr (va : var_exp).

(* TODO: Make this meaningful*)
Definition lookup (x:string) : Z := 1.

Fixpoint ceval (ce : const_exp) : Z :=
  match ce with
  | ConstNum z => z
  | ConstParenExpr ce => ceval ce
  | ConstUnOp uo ce =>
    let v := ceval ce in
      match uo with
     | Positive => id v
     | Negative => - v
     end
  | ConstBinOp ce1 ce2 bo =>
    let v1 := (ceval ce1) in
    let v2 := (ceval ce2) in
      match bo with
      | Plus => v1 + v2
      | Sub => v1 - v2
      | Mul => v1 * v2
      | Div => v1 / v2
      end
end.


Fixpoint veval (va : var_exp) : Z :=
  match va with
  | X x => lookup x
  | Num n => n
  | ParenExpr va => veval va
  | UnOp uo va =>
    let v := veval va in
      match uo with
      | Positive => id v
      | Negative => - v
      end
  | BinOp va1 va2 bo =>
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


Definition eeval (e : exp) : Z :=
  match e with
  | ConstExpr ce => ceval ce
  | VarExpr va => veval va
  end.

Lemma nnzeq : forall z : Z,
  - - z = z.
Proof.
induction z as [].
- (* 0 *)     simpl. reflexivity.
- (* z > 0 *) simpl. reflexivity.
- (* z < 0 *) simpl. reflexivity.
Qed.

(* Proof that the negation is involute in our language; i.e.,
that applying the unary operation negate to a constant expression twice
results in the same value.*)
Theorem neg_neg_equal_ce : forall ce : const_exp,
ceval (ConstUnOp Negative (ConstUnOp Negative ce)) = ceval ce.
Proof.
  induction ce as [].
  - (* ConstNum *)        simpl. rewrite nnzeq. reflexivity.
  - (* ConstParentExpr *) simpl. rewrite nnzeq. reflexivity.
  - (* ConstUnOp *)       simpl. rewrite nnzeq. reflexivity.
  - (* ConstBinOp *)      simpl. rewrite nnzeq. reflexivity.
Qed.
