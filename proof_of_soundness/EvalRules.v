Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  ConfigVars
  Syntax.


(* Macro substitution.
   Check this for details on nested calls to macros:
   https://gcc.gnu.org/onlinedocs/cpp/Argument-Prescan.html
   Currently we don't supported macro calls in macro arguments.
 *)
Fixpoint msub
  (p : string) (e : expr) (mexpr : expr) : expr :=
  match mexpr with
  | Num z => Num z
  | Var x =>
    match (p =? x)%string with
    | true => e
    | false => Var x
    end
  | ParenExpr e0 => ParenExpr (msub p e e0)
  | UnExpr uo e0 => UnExpr uo (msub p e e0)
  | BinExpr bo e1 e2 => BinExpr bo (msub p e e1) (msub p e e2)
    (* TODO: Fix these two once we add pointers *)
  | Assign x e0 => match (p =? x)%string with
    (* Right now we only substitute the LHS of assignments if
       the expression to plug in is also simply a variable *)
    | true => match e with
      | (Var y) => Assign y (msub p e e0)
      | _ => Assign x (msub p e e0)
      end
    | _ => Assign x (msub p e e0)
    end
  (* FIXME: This doesn't match the actual semantics of macro expansion
            See the Google Doc *)
  | CallOrInvocation x es => CallOrInvocation x es
end.

Inductive MSub : string -> expr -> expr -> expr -> Prop :=
  | MS_Num : forall p e z,
    MSub p e (Num z) (Num z)
  | MS_Var_Replace : forall p e x,
    p = x ->
    MSub p e (Var x) e
  | MS_Var_No_Replace : forall p e x,
    p <> x ->
    MSub p e (Var x) (Var x)
  | MS_PareExpr : forall p e e0 e0',
    MSub p e e0 e0' ->
    MSub p e (ParenExpr e0) (ParenExpr e0')
  | MS_UnExpr : forall p e uo e0 e0',
    MSub p e e0 e0' ->
    MSub p e (UnExpr uo e0) (UnExpr uo e0')
  | MS_BinExpr : forall p e bo e1 e2 e1' e2',
    MSub p e e1 e1' ->
    MSub p e e2 e2' ->
    MSub p e (BinExpr bo e1 e2) (BinExpr bo e1' e2')
  | MS_Assign_Replace : forall p e x y e0 e0',
    p = x ->
    e = Var y ->
    MSub p e e0 e0' ->
    MSub p e (Assign x e0) (Assign y e0')
  | MS_Assign_No_Replace : forall p e x e0 e0',
    p <> x ->
    MSub p e e0 e0' ->
    MSub p e (Assign x e0) (Assign x e0')
  | MS_Call_Or_Invocation : forall p e x es es',
    MSubList p e es es' ->
    MSub p e (CallOrInvocation x es) (CallOrInvocation x es')
with MSubList : string -> expr -> list expr -> list expr -> Prop :=
  | MSL_nil : forall p e,
    MSubList p e nil nil
  | MSL_cons : forall p e e0 e0' es0 es0',
    MSub p e e0 e0' ->
    MSubList p e es0 es0' ->
    MSubList p e (e0::es0) (e0'::es0').


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
  - rewrite Bool.orb_false_iff in H. apply Classical_Prop.and_not_or. split.
    + apply IHe1. apply H.
    + apply IHe2. apply H.
  - apply Classical_Prop.not_or_and in H. apply Bool.orb_false_iff. split.
    + apply IHe1. apply H.
    + apply IHe2. apply H.
Qed.


Inductive NoVarsInEnvironment : expr -> environment -> Prop :=
  | NV_Num : forall z E,
    NoVarsInEnvironment (Num z) E
  | NV_Var : forall x E,
    ~ StringMap.In x E ->
    NoVarsInEnvironment (Var x) E
  | NV_ParenExpr : forall e0 E,
    NoVarsInEnvironment e0 E ->
    NoVarsInEnvironment (ParenExpr e0) E
  | NV_UnExpr : forall uo e0 E,
    NoVarsInEnvironment e0 E ->
    NoVarsInEnvironment (UnExpr uo e0) E
  | NV_Bin_Expr : forall bo e1 e2 E,
    NoVarsInEnvironment e1 E ->
    NoVarsInEnvironment e2 E ->
    NoVarsInEnvironment (BinExpr bo e1 e2) E
  | NV_Assign : forall x e0 E,
    ~ StringMap.In x E ->
    NoVarsInEnvironment e0 E ->
    NoVarsInEnvironment (Assign x e0) E
  | NV_CallOrInvocation : forall x es E,
    ~ StringMap.In x E ->
    NoVarsInEnvironmentArgs es E ->
    NoVarsInEnvironment (CallOrInvocation x es) E
with NoVarsInEnvironmentArgs : list expr -> environment -> Prop :=
  | NV_Args_nil : forall E,
    NoVarsInEnvironmentArgs nil E
  | NV_Args_cons : forall e es E,
    NoVarsInEnvironment e E ->
    NoVarsInEnvironmentArgs es E ->
    NoVarsInEnvironmentArgs (e::es) E.


Inductive NoMacroInvocations : expr -> function_table -> macro_table -> Prop :=
  | NM_Num : forall z F M,
    NoMacroInvocations (Num z) F M
  | NM_Var : forall x F M,
    NoMacroInvocations (Var x) F M
  | NM_ParenExpr : forall e0 F M,
    NoMacroInvocations e0 F M ->
    NoMacroInvocations (ParenExpr e0) F M
  | NM_UnExpr : forall uo e0 F M,
    NoMacroInvocations e0 F M ->
    NoMacroInvocations (UnExpr uo e0) F M
  | NM_Bin_Expr : forall bo e1 e2 F M,
    NoMacroInvocations e1 F M ->
    NoMacroInvocations e2 F M ->
    NoMacroInvocations (BinExpr bo e1 e2) F M
  | NM_Assign : forall x e0 F M,
    NoMacroInvocations e0 F M ->
    NoMacroInvocations (Assign x e0) F M
  | NM_CallOrInvocation : forall x es F M params fstmt fexpr,
    ~ StringMap.In x M ->
    NoMacroInvocationsArgs es F M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    NoMacroInvocations fexpr F M ->
    NoMacroInvocations (CallOrInvocation x es) F M
with NoMacroInvocationsArgs : list expr -> function_table -> macro_table -> Prop :=
  | NM_Args_nil : forall F M,
    NoMacroInvocationsArgs nil F M
  | NM_Args_cons : forall e es F M,
    NoMacroInvocations e F M ->
    NoMacroInvocationsArgs es F M ->
    NoMacroInvocationsArgs (e::es) F M.


(* Right now, a term that fails to evaluate will simply get "stuck";
   i.e. it will fail to be reduced further. *)
Inductive EvalExpr:
  store -> environment -> environment ->
  function_table -> macro_table ->
  expr ->
  Z -> store -> Prop :=
  (* Numerals evaluate to their integer representation and do not
     change the store *)
  | E_Num : forall S E G F M z,
    EvalExpr S E G F M (Num z) z S
  (* Variable lookup occurs iff a macro parameter is not found. *)
  | E_LocalVar : forall S E G F M x l v,
    StringMap.MapsTo x l E ->
    NatMap.MapsTo l v S ->
    EvalExpr S E G F M (Var x) v S
  (* Local variables shadow global variables, so only if a local
     variable lookup fails do we check the global environment. *)
  | E_GlobalVar : forall S E G F M x l v,
    ~ StringMap.In x E->
    StringMap.MapsTo x l G ->
    NatMap.MapsTo l v S ->
    EvalExpr S E G F M (Var x) v S
  (* Parenthesized expressions evaluate to themselves. *)
  | E_ParenExpr : forall S E G F M e0 v S',
    EvalExpr S E G F M e0 v S' ->
    EvalExpr S E G F M (ParenExpr e0) v S'
  (* Unary expressions *)
  | E_UnExpr : forall S E G F M S' uo e0 v,
    EvalExpr S E G F M e0 v S' ->
    EvalExpr S E G F M (UnExpr uo e0) ((unop_to_op uo) v) S'
  (* Binary expressions. Left operands are evaluated first. *)
  (* NOTE: Evaluation rules do not handle operator precedence.
     The parser must use a concrete syntax to generate a parse tree
     with the appropriate precedence levels in it. *)
  | E_BinExpr : forall S E G F M bo e1 e2 v1 v2 S' S'',
    EvalExpr S E G F M e1 v1 S' ->
    EvalExpr S' E G F M e2 v2 S'' ->
    EvalExpr S E G F M (BinExpr bo e1 e2) ((binop_to_op bo) v1 v2) S''
  (* Variable assignments update the store by adding a new L-value to
     R-value mapping or by overriding an existing one.
     The R-value is returned along with the updated state.
     For now we assume that there is no overlap between macro parameters
     and variables that are assigned to (i.e., it is impossible for a
     macro to have side-effects). *)
  (* Local variable assignment overrides global variable assignment. *)
  | E_Assign_Local : forall S E G F M l x e0 v S' S'',
    StringMap.MapsTo x l E ->
    EvalExpr S E G F M e0 v S' ->
    S'' = NatMapProperties.update S (NatMap.add l v (NatMap.empty Z)) ->
    EvalExpr S E G F M (Assign x e0) v S''
  (* Global variable assignment *)
  | E_Assign_Global : forall S E G F M l x e0 v S' S'',
    ~ StringMap.In x E ->
    StringMap.MapsTo x l G ->
    EvalExpr S E G F M e0 v S' ->
    S'' = NatMapProperties.update S (NatMap.add l v (NatMap.empty Z)) ->
    EvalExpr S E G F M (Assign x e0) v S''
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
           Ef Sargs S' S'' S''' S'''' S''''' v vs l,
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
    EvalArgs S E G F M params es vs S' Ef Sargs l ->
    (* Create the function environment *)
    StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->
    (* Create a store for mapping L-values to the arguments to in the store.
       Possibly provable but easier to just assert here *)
    NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) ->
    (* All the L-values used in the argument store do not appear in the original store.
       We could possibly prove this, but it is easier to put it here. *)
    NatMapProperties.Disjoint S' Sargs ->
    (* Combine the argument store into the original store *)
    S'' = NatMapProperties.update S' Sargs ->
    (* Evaluate the function's body *)
    EvalStmt S'' Ef G F M fstmt S''' ->
    EvalExpr S''' Ef G F M fexpr v S'''' ->
    (* Only keep in the store the L-value mappings that were there when
       the function was called; i.e., remove from the store all mappings
       whose L-value is in Ef/Sargs. *)
    NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
    EvalExpr S E G F M (CallOrInvocation x es) v S'''''
  (* Macro invocation *)
  | E_MacroInvocation :
    forall S E G F M x params es mexpr M' ef S' v,
    (* TODO: Things to consider:
     - How to handle nested macros?
     *)
    (* Macro definitions shadow function definitions, so if a macro
       definition is found, we don't even check the function list.
       However, when we execute the macro's body, we need to remove
       the current macro definition from the list of macro definitions
       to avoid nested macros from being expanded. *)
    StringMap.MapsTo x (params, mexpr) M ->
    M' = StringMap.remove x M ->
    NoDup params ->
    MacroSubst params es mexpr ef ->
    EvalExpr S E G F M' ef v S' ->
    EvalExpr S E G F M (CallOrInvocation x es) v S'
with EvalArgs :
  store -> environment -> environment -> function_table -> macro_table ->
  list string -> list expr -> list Z -> store -> environment -> store ->
  nat ->
  Prop :=
  (* End of arguments *)
  | EvalArgs_nil : forall Sprev Ecaller G F M,
    EvalArgs Sprev Ecaller G F M nil nil nil Sprev (StringMap.empty nat) (NatMap.empty Z) 0
  (* There are arguments left to evaluate *)
  | EvalArgs_cons : forall Sprev Ecaller G F M p e v Snext ps es vs Sfinal l Ef' Sargs',
    (* Evaluate the first expression using the caller's environment *)
    EvalExpr Sprev Ecaller G F M e v Snext ->
    (* Evaluate the remaining expressions *)
    EvalArgs Snext Ecaller G F M ps es vs Sfinal Ef' Sargs' l ->
    (* The L-value to add is not in the store *)
    ~ NatMap.In l Sargs' ->
    (* The parameter to add is not in the environment *)
    NoDup (p::ps) ->
    ~ StringMap.In p Ef' ->
    (* Return the final environment *)
    EvalArgs  Sprev Ecaller G F M (p::ps) (e::es) (v::vs) Sfinal
              (StringMap.add p l Ef') (NatMap.add l v Sargs') (S l)
with MacroSubst :
  list string -> list expr -> expr -> expr -> Prop :=
  | MacroSubst_nil : forall mexpr,
    MacroSubst nil nil mexpr mexpr
  | MacroSubst_cons : forall p e ps es mexpr ef ef',
    MSub p e mexpr ef ->
    MacroSubst ps es ef ef' ->
    MacroSubst (p::ps) (e::es) mexpr ef'
with EvalStmt :
  store -> environment -> environment ->
  function_table -> macro_table ->
  stmt ->
  store -> Prop :=
  (* A skip statement does not change the state *)
  | E_Skip : forall S E G F M,
    EvalStmt S E G F M Skip S.


(* Relation only holds if an expression does not contain any calls from the given
   function table F' *)
Inductive ExprNoCallsFromFunctionTable :
  expr -> function_table -> macro_table -> function_table -> Prop :=
  | NC_Num : forall z F M F',
    ExprNoCallsFromFunctionTable (Num z) F M F'
  | NC_Var : forall x F M F',
    ExprNoCallsFromFunctionTable (Var x) F M F'
  | NC_ParenExpr : forall e0 F M F',
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (ParenExpr e0) F M F'
  | NC_UnExpr : forall uo e0 F M F',
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (UnExpr uo e0) F M F'
  | NC_BinExpr : forall bo e1 e2 F M F',
    ExprNoCallsFromFunctionTable e1 F M F' ->
    ExprNoCallsFromFunctionTable e2 F M F' ->
    ExprNoCallsFromFunctionTable (BinExpr bo e1 e2) F M F'
  | NC_Assign : forall x e0 F M F',
    ExprNoCallsFromFunctionTable e0 F M F' ->
    ExprNoCallsFromFunctionTable (Assign x e0) F M F'
  | NC_FunctionCall: forall x es F M F' params fstmt fexpr,
    ~ StringMap.In x M ->
    ~ StringMap.In x F' ->
    ExprNoCallsFromFunctionTableArgs es F M F' ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->
    StmtNoCallsFromFunctionTable fstmt F M F' ->
    ExprNoCallsFromFunctionTable fexpr F M F' ->
    ExprNoCallsFromFunctionTable (CallOrInvocation x es) F M F'
  | NC_MacroInvocation: forall x es F M F' params mexpr ef,
    ~ StringMap.In x F' ->
    ExprNoCallsFromFunctionTableArgs es F M F' ->
    StringMap.MapsTo x (params, mexpr) M ->
    ExprNoCallsFromFunctionTable mexpr F M F' ->
    MacroSubst params es mexpr ef ->
    (* We use (StringMap.remove x M) here because that is what is used in macro invocations *)
    ExprNoCallsFromFunctionTable ef F (StringMap.remove x M) F' ->
    ExprNoCallsFromFunctionTable (CallOrInvocation x es) F M F'
with ExprNoCallsFromFunctionTableArgs :
  list expr -> function_table -> macro_table -> function_table -> Prop :=
  | NC_Args_nil : forall F M F',
    ExprNoCallsFromFunctionTableArgs nil F M F'
  | NC_Args_cons : forall e es F M F',
    ExprNoCallsFromFunctionTable e F M F' ->
    ExprNoCallsFromFunctionTableArgs es F M F' ->
    ExprNoCallsFromFunctionTableArgs (e::es) F M F'
with StmtNoCallsFromFunctionTable :
  stmt -> function_table -> macro_table -> function_table -> Prop :=
  | NC_Skip : forall F M F',
    StmtNoCallsFromFunctionTable Skip F M F'.
