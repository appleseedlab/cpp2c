Require Import
  Coq.Lists.List
  Coq.Strings.String
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  ConfigVars
  Syntax.


Theorem demorgan : forall A B,
  ~ (A \/ B) <-> ~A /\ ~B.
Proof.
  intros. tauto.
Qed.

(* Macro substitution.
   Check this for details on nested calls to macros:
   https://gcc.gnu.org/onlinedocs/cpp/Argument-Prescan.html
   Currently we don't supported macro calls in macro arguments.
 *)
Fixpoint msub
  (MP : macro_parameters) (mexpr : expr) : expr :=
  match mexpr with
  | Num z => Num z
  | Var x =>
    match lookup_macro_parameter MP x with
    | Some pe => snd pe
    | None => Var x
    end
  | ParenExpr e0 => ParenExpr (msub MP e0)
  | UnExpr uo e0 => UnExpr uo (msub MP e0)
  | BinExpr bo e1 e2 => BinExpr bo (msub MP e1) (msub MP e2)
    (* TODO: Fix these two once we add pointers *)
  | Assign x e0 => match lookup_macro_parameter MP x with
    (* Right now we only substitute the LHS of assignments if
       the expression to plug in is also simply a variable *)
    | Some pe => match snd pe with
      | (Var y) => Assign y (msub MP e0)
      | _ => Assign x (msub MP e0)
      end
    | _ => Assign x (msub MP e0)
    end
  (* FIXME: This doesn't match the actual semantics of macro expansion
            See the Google Doc *)
  | CallOrInvocation x es => CallOrInvocation x es
end.


Fixpoint expr_has_side_effects (e: expr) : bool :=
  match e with
  | Num z => false
  | Var x => false
  | ParenExpr e0 => expr_has_side_effects e0
  | UnExpr uo e0 => expr_has_side_effects e0
  | BinExpr bo e1 e2 =>
    orb (expr_has_side_effects e1) (expr_has_side_effects e2)
  (* This is conservative, but matches the behaviour of Clang *)
  | Assign x e0 => true
  | CallOrInvocation x es => true
end.


Fixpoint ExprHasSideEffects (e : expr) : Prop :=
  match e with
  | Num z => False
  | Var x => False
  | ParenExpr e0 => ExprHasSideEffects e0
  | UnExpr uo e0 => ExprHasSideEffects e0
  | BinExpr bo e1 e2 =>
    (ExprHasSideEffects e1) \/ (ExprHasSideEffects e2)
  (* This is conservative, but matches the behaviour of Clang *)
  | Assign x e0 => True
  | CallOrInvocation x es => True
end.


Theorem expr_has_side_effects_ExprHasSideEffects : forall e,
  expr_has_side_effects e = true <-> ExprHasSideEffects e.
Proof.
  split; induction e; intros; simpl in *;
    try discriminate; try (apply IHe; apply H);
    try apply I; try contradiction; try reflexivity.
  - apply Bool.orb_prop in H. tauto.
  - apply Bool.orb_true_iff. tauto.
Qed.


Theorem neg_expr_side_effects_NotExprHasSideEffects : forall e,
  expr_has_side_effects e = false <-> ~ ExprHasSideEffects e.
Proof.
  split; induction e; intros; simpl in *;
  try discriminate; try (apply IHe; apply H);
  try apply I; try contradiction; try reflexivity; try auto.
  - rewrite Bool.orb_false_iff in H. apply demorgan. split.
    + apply IHe1. apply H.
    + apply IHe2. apply H.
  - apply demorgan in H. apply Bool.orb_false_iff. split.
    + apply IHe1. apply H.
    + apply IHe2. apply H.
Qed.

(* Right now, a term that fails to evaluate will simply get "stuck";
   i.e. it will fail to be reduced further.
   We do not provide any error messages, but I think we could add
   this later using a sum type. *)
Inductive ExprEval:
  store -> environment -> environment ->
  function_table -> macro_table ->
  expr ->
  Z -> store -> Prop :=
  (* Numerals evaluate to their integer representation and do not
     change the store *)
  | E_Num : forall S E G F M z,
    ExprEval S E G F M (Num z) z S
  (* Variable lookup occurs iff a macro parameter is not found. *)
  | E_LocalVar : forall S E G F M x l v,
    StringMap.MapsTo x l E ->
    NatMap.MapsTo l v S ->
    ExprEval S E G F M (Var x) v S
  (* Local variables shadow global variables, so only if a local
     variable lookup fails do we check the global environment. *)
  | E_GlobalVar : forall S E G F M x l v,
    ~ StringMap.In x E->
    StringMap.MapsTo x l G ->
    NatMap.MapsTo l v S ->
    ExprEval S E G F M (Var x) v S
  (* Parenthesized expressions evaluate to themselves. *)
  | E_ParenExpr : forall S E G F M e0 v S',
    ExprEval S E G F M e0 v S' ->
    ExprEval S E G F M (ParenExpr e0) v S'
  (* Unary expressions *)
  | E_UnExpr : forall S E G F M S' uo e0 v,
    ExprEval S E G F M e0 v S' ->
    ExprEval S E G F M (UnExpr uo e0) ((unop_to_op uo) v) S'
  (* Binary expressions. Left operands are evaluated first. *)
  (* NOTE: Evaluation rules do not handle operator precedence.
     The parser must use a concrete syntax to generate a parse tree
     with the appropriate precedence levels in it. *)
  | E_BinExpr : forall S E G F M bo e1 e2 v1 v2 S' S'',
    ExprEval S E G F M e1 v1 S' ->
    ExprEval S' E G F M e2 v2 S'' ->
    ExprEval S E G F M (BinExpr bo e1 e2) ((binop_to_op bo) v1 v2) S''
  (* Variable assignments update the store by adding a new L-value to
     R-value mapping or by overriding an existing one.
     The R-value is returned along with the updated state.
     For now we assume that there is no overlap between macro parameters
     and variables that are assigned to (i.e., it is impossible for a
     macro to have side-effects). *)
  (* Local variable assignment overrides global variable assignment. *)
  | E_Assign_Local : forall S E G F M l x e0 v S' S'',
    StringMap.MapsTo x l E ->
    ExprEval S E G F M e0 v S' ->
    S'' = NatMapProperties.update S (NatMap.add l v (NatMap.empty Z)) ->
    ExprEval S E G F M (Assign x e0) v S''
  (* Global variable assignment *)
  | E_Assign_Global : forall S E G F M l x e0 v S' S'',
    ~ StringMap.In x E ->
    StringMap.MapsTo x l G ->
    ExprEval S E G F M e0 v S' ->
    S'' = NatMapProperties.update S (NatMap.add l v (NatMap.empty Z)) ->
    ExprEval S E G F M (Assign x e0) v S'
  (* For function calls, we perform the following steps:
     1) Evaluate arguments
     2) Map parameters to arguments in function local environment,
        which is based on the global environment
     3) Evaluate the function's statement
     4) Evaluate the function's return expression
     4.5) Remove the mappings that were added to the store for the function
          call
     5) Return the return value and store *)
  | E_FunctionCall:
    forall S E G F M x es params fstmt fexpr ls
           Sargs S' S'' S''' Ef S'''' S''''' v vs,
    (* TODO: Things to consider :
       - Should all functions have unique names?
    *)
    (* Macro definitions shadow function definitions, so function calls
       only occur if a macro definition is not found *)
    ~ StringMap.In x M ->
    (* Function name maps to some function *)
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    (* Parameters should all be unique *)
    NoDup params ->
    (* Evaluate the function's arguments *)

    EvalArgs S E G F M es vs S' ->
    (* Create the function environment *)
    StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->
    (* Create a store for mapping L-values to the arguments to in the store *)
    NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) ->
    (* All the L-values used in the argument store do not appear in the original store *)
    NatMapProperties.Disjoint S' Sargs ->
    (* Combine the argument store into the original store *)
    NatMap.Equal S'' (NatMapProperties.update S' Sargs) ->
    (* Evaluate the function's body *)
    StmtEval S'' Ef G F M fstmt S''' ->
    ExprEval S''' Ef G F M fexpr v S'''' ->
    (* Only keep in the store the L-value mappings that were there when
       the function was called; i.e., remove from the store all mappings
       whose L-value is in Ef/Sargs. *)
    NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
    ExprEval S E G F M (CallOrInvocation x es) v S'''''
  (* Macro invocation *)
  | E_MacroInvocation :
    forall S E G F M x params es mexpr M' MP ef S' v,
    (* TODO: Things to consider:
     - How to handle nested macros?
     - |params| == |es|?
     - Should all macros have unique names?
     *)
    (* Macro definitions shadow function definitions, so if a macro
       definition is found, we don't even check the function list.
       However, when we execute the macro's body, we need to remove
       the current macro definition from the list of macro definitions
       to avoid nested macros from being expanded. *)
    StringMap.MapsTo x (params, mexpr) M ->
    M' = StringMap.remove x M ->
    NoDup params ->
    (* Create the MP for evaluating the macro expression in *)
    MP = combine params es ->
    ef = msub MP mexpr ->
    ExprEval S E G F M' ef v S' ->
    ExprEval S E G F M' (CallOrInvocation x es) v S'
with EvalArgs :
  store -> environment -> environment -> function_table -> macro_table ->
  list expr -> list Z -> store ->
  Prop :=
  (* End of arguments *)
  | E_EmptyArgs : forall Sprev Ecaller G F M vs (Snext : store),
    EvalArgs Sprev Ecaller G F M nil vs Sprev
  (* There are arguments left to evaluate *)
  | E_NonEmptyArgs : forall Sprev Ecaller G F M e v Snext es vs Sfinal,
    (* Evaluate the first expression using the caller's *)
    ExprEval Sprev Ecaller G F M e v Snext ->
    (* Evaluate the remaining expressions *)
    EvalArgs Snext Ecaller G F M es vs Sfinal ->
    (* Return the final environment *)
    EvalArgs Sprev Ecaller G F M (e::es) (v::vs) Sfinal
with StmtEval :
  store -> environment -> environment ->
  function_table -> macro_table ->
  stmt ->
  store -> Prop :=
  (* A skip statement does not change the state *)
  | E_Skip : forall S E G F M,
    StmtEval S E G F M Skip S.
