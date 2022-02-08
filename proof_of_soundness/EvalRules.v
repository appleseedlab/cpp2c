Require Import
  Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  ConfigVars
  MapTheorems
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


(* Right now, a term that fails to evaluate will simply get "stuck";
   i.e. it will fail to be reduced further. *)
Inductive EvalExpr:
  store -> environment -> environment ->
  function_table -> macro_table ->
  expr ->
  Z -> store -> Prop :=
  (* Numerals evaluate to their integer representation and do not
     change the store *)
  | E_Num : forall S E G F M z S',
    NatMap.Equal S S' ->
    EvalExpr S E G F M (Num z) z S'
  (* Local variable lookup *)
  | E_LocalVar : forall S E G F M x l v S',
    (* Store does not change *)
    NatMap.Equal S S' ->
    (* Variable is found in local environment *)
    StringMap.MapsTo x l E ->
    (* L-value maps to an R-value *)
    NatMap.MapsTo l v S ->
    EvalExpr S E G F M (Var x) v S'
  (* Global variable lookup *)
  | E_GlobalVar : forall S E G F M x l v S',
    (* Store does not change *)
    NatMap.Equal S S' ->
  (* Local variables shadow global variables, so only if a local
     variable lookup fails do we check the global environment. *)
    ~ StringMap.In x E->
    (* Variable is found in global environment *)
    StringMap.MapsTo x l G ->
    (* L-value maps to R-value *)
    NatMap.MapsTo l v S ->
    EvalExpr S E G F M (Var x) v S'
  (* Parenthesized expressions evaluate to themselves. *)
  | E_ParenExpr : forall S E G F M e0 v S',
    (* Evaluate the inner expression *)
    EvalExpr S E G F M e0 v S' ->
    EvalExpr S E G F M (ParenExpr e0) v S'
  (* Unary expressions *)
  | E_UnExpr : forall S E G F M S' uo e0 v,
    (* Evaluate the inner expression *)
    EvalExpr S E G F M e0 v S' ->
    (* Perform the unary operations on the value obtained *)
    EvalExpr S E G F M (UnExpr uo e0) ((unop_to_op uo) v) S'
  (* Binary expressions. Left operands are evaluated first. *)
  (* NOTE: Evaluation rules do not handle operator precedence.
     The parser must use a concrete syntax to generate a parse tree
     with the appropriate precedence levels in it. *)
  | E_BinExpr : forall S E G F M bo e1 e2 v1 v2 S' S'',
    (* Evaluate the left operand *)
    EvalExpr S E G F M e1 v1 S' ->
    (* Evaluate the right operand *)
    EvalExpr S' E G F M e2 v2 S'' ->
    (* Perform the binary operation on the values obtained *)
    EvalExpr S E G F M (BinExpr bo e1 e2) ((binop_to_op bo) v1 v2) S''
  (* Variable assignments update the store by adding a new L-value to
     R-value mapping or by overriding an existing one.
     The R-value is returned along with the updated state. *)
  (* Local variable assignment overrides global variable assignment. *)
  | E_Assign_Local : forall S E G F M l x e0 v S' S'',
    StringMap.MapsTo x l E ->
    EvalExpr S E G F M e0 v S' ->
    NatMap.Equal S'' (NatMapProperties.update S (NatMap.add l v (NatMap.empty Z))) ->
    EvalExpr S E G F M (Assign x e0) v S''
  (* Global variable assignment *)
  | E_Assign_Global : forall S E G F M l x e0 v S' S'',
    ~ StringMap.In x E ->
    StringMap.MapsTo x l G ->
    EvalExpr S E G F M e0 v S' ->
    NatMap.Equal S'' (NatMapProperties.update S (NatMap.add l v (NatMap.empty Z))) ->
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
    forall S E G F M x es params fstmt fexpr l ls
           Ef Sargs S' S'' S''' S'''' S''''' v vs,
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
    EvalExprList S E G F M params es vs S' Ef Sargs l ls ->
    (* Create the function environment *)
    StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->
    (* Create a store for mapping L-values to the arguments to in the store.
       Possibly provable but easier to just assert here *)
    NatMap.Equal Sargs (NatMapProperties.of_list (combine ls vs)) ->
    (* All the L-values used in the argument store do not appear in the original store.
       We could possibly prove this, but it is easier to put it here. *)
    NatMapProperties.Disjoint S' Sargs ->
    (* Combine the argument store into the original store *)
    NatMap.Equal S'' (NatMapProperties.update S' Sargs) ->
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
    (* Remove the macro from the macro table to avoid recursively
       expanding macros. We could express this using StringMap.Equal,
       but it is easier for the proof if we Logic.eq instead. *)
    M' = (StringMap.remove x M) ->
    (* No duplicate parameters *)
    NoDup params ->
    (* Perform the macro substitution *)
    MacroSubst params es mexpr ef ->
    (* Evalue the fully-substituted macro body
       under the caller's environment *)
    EvalExpr S E G F M' ef v S' ->
    EvalExpr S E G F M (CallOrInvocation x es) v S'
with EvalExprList :
  store -> environment -> environment -> function_table -> macro_table ->
  list string -> list expr -> list Z -> store -> environment -> store ->
  nat -> list nat -> Prop :=
  (* End of arguments *)
  | E_ExprList_nil : forall Sprev Ecaller G F M Snext,
    NatMap.Equal Sprev Snext ->
    EvalExprList Sprev Ecaller G F M nil nil nil Snext (StringMap.empty nat) (NatMap.empty Z)
      1 (0 :: nil)
  (* There are arguments left to evaluate *)
  | E_ExprList_cons : forall Sprev Ecaller G F M p e v Snext ps es vs Sfinal Ef' Sargs' l ls,
    (* Evaluate the first expression using the caller's environment *)
    EvalExpr Sprev Ecaller G F M e v Snext ->
    (* Evaluate the remaining expressions *)
    EvalExprList Snext Ecaller G F M ps es vs Sfinal Ef' Sargs' l ls ->
    (* The L-value to add is not in the store *)
    ~ NatMap.In l Sargs' ->
    (* The parameter to add is not in the environment *)
    NoDup (p::ps) ->
    ~ StringMap.In p Ef' ->
    (* Return the final environment *)
    EvalExprList  Sprev Ecaller G F M (p::ps) (e::es) (v::vs) Sfinal
                  (StringMap.add p l Ef') (NatMap.add l v Sargs') l ( l :: ls)
with MacroSubst :
  list string -> list expr -> expr -> expr -> Prop :=
  | MacroSubst_nil : forall mexpr,
    (* No more substitutions necessary *)
    MacroSubst nil nil mexpr mexpr
  | MacroSubst_cons : forall p e ps es mexpr ef ef',
    (* Substitute the first argument *)
    MSub p e mexpr ef ->
    (* Substitute the remaining arguments *)
    MacroSubst ps es ef ef' ->
    (* Return the fully-substituted expression *)
    MacroSubst (p::ps) (e::es) mexpr ef'
with EvalStmt :
  store -> environment -> environment ->
  function_table -> macro_table ->
  stmt ->
  store -> Prop :=
  (* A skip statement does not change the state *)
  | E_Skip : forall S E G F M S',
    NatMap.Equal S S' ->
    EvalStmt S E G F M Skip S'.


Scheme MSub_mut := Induction for MSub Sort Prop
with MSubList_mut := Induction for MSubList Sort Prop.


Lemma MSub_deterministic : forall p e mexpr ef,
  MSub p e mexpr ef ->
  forall ef0,
  MSub p e mexpr ef0 ->
  ef = ef0.
Proof.
  apply (MSub_mut
    (fun p e mexpr ef (h : MSub p e mexpr ef) =>
      forall ef0,
      MSub p e mexpr ef0 ->
      ef = ef0)
    (fun p e es es' (h : MSubList p e es es') =>
      forall es'0,
      MSubList p e es es'0 ->
      es' = es'0)); intros; auto.
  - inversion_clear H; auto.
  - inversion_clear H; auto. contradiction.
  - inversion_clear H. contradiction. auto.
  - inversion_clear H0. f_equal. auto.
  - inversion_clear H0. f_equal. auto.
  - inversion_clear H1. f_equal. auto. auto.
  - inversion_clear H0; f_equal.
    + subst e. injection H2. auto.
    + subst e. injection H2. auto.
    + contradiction.
    + contradiction.
  - inversion_clear H0.
    + contradiction.
    + f_equal. auto.
  - inversion_clear H0. f_equal. auto.
  - inversion_clear H. auto.
  - inversion_clear H1.
    assert (e0' = e0'0). { auto. }
    assert ( es0' = es0'0). { auto. }
    subst. auto.
Qed.


Lemma MacroSubst_deterministic : forall params es mexpr ef,
  MacroSubst params es mexpr ef ->
  forall ef0,
  MacroSubst params es mexpr ef0 ->
  ef = ef0.
Proof.
  intros params es mexpe ef H. induction H; intros.
  - inversion H. auto.
  - inversion_clear H1.
    assert (ef = ef1).
    { apply MSub_deterministic with p e mexpr; auto. }
    subst ef1. apply IHMacroSubst. auto.
Qed.


Lemma MSub_mexpr_Num_ef_Num : forall p e z ef,
  MSub p e (Num z) ef ->
  ef = Num z.
Proof.
  intros. remember (Num z). induction H; try discriminate.
  - auto.
Qed.


Lemma MacroSubst_mexpr_Num_ef_Num : forall params es z ef,
  MacroSubst params es (Num z) ef ->
  ef = Num z.
Proof.
  intros. remember (Num z). induction H.
  - (* MacroSubst nil *)
    auto.
  - (* MacroSubst cons *)
    subst. apply MSub_mexpr_Num_ef_Num in H. subst.
    auto.
Qed.


(* The following lemmas involve all parts of program evaluation
   (e.g., expression, argument list, and statement evaluation).
   Coq's built-in induction tactic is not powerful enough to provide
   us with the induction hypotheses necessary to prove these lemmas, so
   we must define our own induction schema for these proofs *)
Scheme EvalExpr_mut := Induction for EvalExpr Sort Prop
with EvalStmt_mut := Induction for EvalStmt Sort Prop
with EvalExprList_mut := Induction for EvalExprList Sort Prop.


Lemma EvalStmt_notin_F_add_EvalStmt : forall S E G F M stmt S',
  EvalStmt S E G F M stmt S' ->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalStmt S E G (StringMap.add x fdef F) M stmt S'.
Proof.
(*
  This proof could be solved instead with the following ltac code:
    intros. induction H; try constructor.
  Instead I have opted to use our custom schema here so that it may serve
  as a simple demonstration of how to use schemas *)
  intros. apply (
    (* First we apply the appropriate schema like a tactic *)
    EvalStmt_mut
      (* Then we have to define a custom inductive hypothesis for each Prop
         that the one we are inducting over is mutually inductive with
         (in this case just the EvalStmt Prop since statement evaluation
         currently only includes skip statements, which don't
         involve expressions) *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S') =>
        EvalStmt S E G (StringMap.add x fdef F) M stmt S')
  ); try constructor; auto.
Qed.


Lemma EvalStmt_Disjoint_update_F_EvalStmt : forall S E G F M stmt S',
  EvalStmt S E G F M stmt S' ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalStmt S E G (StringMapProperties.update F F') M stmt S'.
Proof.
  intros. induction H; try constructor. auto.
Qed.


Lemma EvalExpr_notin_F_add_EvalExpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalExpr S E G (StringMap.add x fdef F) M e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalExpr S E G (StringMap.add x fdef F) M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalStmt S E G (StringMap.add x fdef F) M stmt S' )
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalExprList Sprev Ecaller G (StringMap.add x fdef F) M ps es vs Snext Ef Sargs l ls)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply E_ExprList_cons with Snext; auto.
Qed.


Lemma EvalExpr_Disjoint_update_F_EvalExpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalExpr S E G (StringMapProperties.update F F') M e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExpr S E G (StringMapProperties.update F F') M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalStmt S E G (StringMapProperties.update F F') M stmt S' )
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExprList Sprev Ecaller G (StringMapProperties.update F F') M ps es vs Snext Ef Sargs l ls)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + apply StringMapProperties.update_mapsto_iff. right. split.
      * auto.
      * apply StringMap_mapsto_in in m.
        unfold StringMapProperties.Disjoint in H2.
        assert (~ (StringMap.In (elt:=function_definition) x F /\
                    StringMap.In (elt:=function_definition) x F')).
        { apply H2. }
        apply Classical_Prop.not_and_or in H3. destruct H3.
        -- contradiction.
        -- auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply E_ExprList_cons with Snext; auto.
Qed.


Lemma EvalExpr_Disjoint_diff_F_EvalExpr : forall S E G F M e v S',
  EvalExpr S E G F M e v S' ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalExpr S E G (StringMapProperties.diff F F') M e v S'.
Proof.
  apply (
    EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExpr S E G (StringMapProperties.diff F F') M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalStmt S E G (StringMapProperties.diff F F') M stmt S' )
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExprList Sprev Ecaller G (StringMapProperties.diff F F') M ps es vs Snext Ef Sargs l ls)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + apply StringMapProperties.diff_mapsto_iff. split.
      * auto.
      * apply StringMap_mapsto_in in m.
        unfold StringMapProperties.Disjoint in H2.
        assert (~ (StringMap.In (elt:=function_definition) x F /\
                    StringMap.In (elt:=function_definition) x F')).
        { apply H2. }
        apply Classical_Prop.not_and_or in H3. destruct H3.
        -- contradiction.
        -- auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply E_ExprList_cons with Snext; auto.
Qed.


Lemma EvalExprList_notin_F_add_EvalExprList : forall S E G F M ps es vs S' Ef Sargs l ls,
  EvalExprList S E G F M ps es vs S' Ef Sargs l ls ->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalExprList S E G (StringMap.add x fdef F) M ps es vs S' Ef Sargs l ls.
Proof.
  apply (
    EvalExprList_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalExpr S E G (StringMap.add x fdef F) M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalStmt S E G (StringMap.add x fdef F) M stmt S' )
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalExprList Sprev Ecaller G (StringMap.add x fdef F) M ps es vs Snext Ef Sargs l ls)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply E_ExprList_cons with Snext; auto.
Qed.


Lemma EvalExprList_Disjoint_update_F_EvalExprList : forall S E G F M ps es vs S' Ef Sargs l ls,
  EvalExprList S E G F M ps es vs S' Ef Sargs l ls ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalExprList S E G (StringMapProperties.update F F') M ps es vs S' Ef Sargs l ls .
Proof.
  apply (
    EvalExprList_mut
      (* EvalExpr *)
      (fun S E G F M e v S' (h : EvalExpr S E G F M e v S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExpr S E G (StringMapProperties.update F F') M e v S' )
      (* EvalStmt *)
      (fun S E G F M stmt S' (h : EvalStmt S E G F M stmt S' ) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalStmt S E G (StringMapProperties.update F F') M stmt S' )
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls
      (h : EvalExprList Sprev Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalExprList Sprev Ecaller G (StringMapProperties.update F F') M ps es vs Snext Ef Sargs l ls)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
    + apply StringMapProperties.update_mapsto_iff. right. split.
      * auto.
      * apply StringMap_mapsto_in in m.
        unfold StringMapProperties.Disjoint in H2.
        assert (~ (StringMap.In (elt:=function_definition) x F /\
                    StringMap.In (elt:=function_definition) x F')).
        { apply H2. }
        apply Classical_Prop.not_and_or in H3. destruct H3.
        -- contradiction.
        -- auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply E_ExprList_cons with Snext; auto.
Qed.


Lemma EvalExpr_Var_x_in_E_or_G : forall S E G F M x v S',
  EvalExpr S E G F M (Var x) v S' ->
  StringMap.In x E \/ StringMap.In x G.
Proof.
  intros. inversion_clear H.
  - left. apply StringMap_mapsto_in in H1. auto.
  - right. apply StringMap_mapsto_in in H2. auto.
Qed.


Lemma S_Equal_EvalExpr : forall S_1 E G F M e v S',
  EvalExpr S_1 E G F M e v S' ->
  forall S_2,
  NatMap.Equal S_1 S_2 ->
  EvalExpr S_2 E G F M e v S'.
Proof.
  apply (EvalExpr_mut
      (* EvalExpr *)
      (fun S_1 E G F M e v S' (h : EvalExpr S_1 E G F M e v S' ) =>
        forall S_2,
        NatMap.Equal S_1 S_2 ->
        EvalExpr S_2 E G F M e v S')
      (* EvalStmt *)
      (fun S_1 E G F M stmt S' (h : EvalStmt S_1 E G F M stmt S' ) =>
        forall S_2,
        NatMap.Equal S_1 S_2 ->
        EvalStmt S_2 E G F M stmt S')
      (* EvalExprList *)
      (fun S_1 Ecaller G F M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList S_1 Ecaller G F M ps es vs Snext Ef Sargs l ls) =>
        forall S_2,
        NatMap.Equal S_1 S_2 ->
        EvalExprList S_2 Ecaller G F M ps es vs Snext Ef Sargs l ls)
    ); intros.
  - (* Num *)
    rewrite H in e. constructor; auto.
  - (* Local var *)
    rewrite H in e. apply E_LocalVar with l; auto. rewrite <- H; auto.
  - (* Global var *)
     rewrite H in e; apply E_GlobalVar with l; auto. rewrite <- H; auto.
  - (* ParenExpr *)
     constructor. apply H; auto.
  - (* UnExpr *)
     constructor. apply H; auto.
  - (* BinExpr *)
      apply E_BinExpr with S'.
      * (* Left operand *)
        apply H. auto.
      * (* Right operand *)
        apply H0; reflexivity.
  - (* Local assignment *)
    rewrite H0 in e1. apply E_Assign_Local with l S'; auto.
  - (* Global assignment *)
    rewrite H0 in e1. apply E_Assign_Global with l S'; auto.
  - (* Function call *)
    rewrite H2 in e5.
    apply E_FunctionCall with params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
  - (* Macro invocation *)
    apply E_MacroInvocation with params mexpr M' ef; auto.
  - (* Statements *)
    constructor. rewrite H in e; auto.
  - (* ExprList (nil) *)
    constructor. rewrite H in e; auto.
  - (* ExprList (cons) *)
    apply E_ExprList_cons with Snext; auto.
Qed.


Lemma S'_Equal_EvalExpr : forall S E G F M e v S'_1,
  EvalExpr S E G F M e v S'_1 ->
  forall S'_2,
  NatMap.Equal S'_1 S'_2 ->
  EvalExpr S E G F M e v S'_2.
Proof.
  apply (EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v S'_1 (h : EvalExpr S E G F M e v S'_1 ) =>
        forall S'_2,
        NatMap.Equal S'_1 S'_2 ->
        EvalExpr S E G F M e v S'_2)
      (* EvalStmt *)
      (fun S E G F M stmt S'_1 (h : EvalStmt S E G F M stmt S'_1 ) =>
        forall S'_2,
        NatMap.Equal S'_1 S'_2 ->
        EvalStmt S E G F M stmt S'_2)
      (* EvalExprList *)
      (fun S Ecaller G F M ps es vs Snext_1 Ef Sargs l ls
        (h : EvalExprList S Ecaller G F M ps es vs Snext_1 Ef Sargs l ls) =>
        forall Snext_2,
        NatMap.Equal Snext_1 Snext_2 ->
        EvalExprList S Ecaller G F M ps es vs Snext_2 Ef Sargs l ls)
    ); intros.
  - (* Num *)
    rewrite H in e. constructor; auto.
  - (* Local var *)
    rewrite H in e. apply E_LocalVar with l; auto.
  - (* Global var *)
     rewrite H in e; apply E_GlobalVar with l; auto.
  - (* ParenExpr *)
     constructor. apply H; auto.
  - (* UnExpr *)
     constructor. apply H; auto.
  - (* BinExpr *)
      apply E_BinExpr with S'.
      * (* Left operand *)
        apply H. reflexivity.
      * (* Right operand *)
        apply H0. auto.
  - (* Local assignment *)
    rewrite H0 in e1. apply E_Assign_Local with l S'; auto.
  - (* Global assignment *)
    rewrite H0 in e1. apply E_Assign_Global with l S'; auto.
  - (* Function call *)
    rewrite H2 in e5.
    apply E_FunctionCall with params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
  - (* Macro invocation *)
    apply E_MacroInvocation with params mexpr M' ef; auto.
  - (* Statements *)
    constructor. rewrite H in e; auto.
  - (* ExprList (nil) *)
    constructor. rewrite H in e; auto.
  - (* ExprList (cons) *)
    apply E_ExprList_cons with Snext; auto.
Qed.


Lemma S_Equal_EvalExprList : forall S_1 Ecaller G F M ps es vs Snext Ef Sargs l ls,
  EvalExprList S_1 Ecaller G F M ps es vs Snext Ef Sargs l ls ->
  forall S_2,
  NatMap.Equal S_1 S_2 ->
  EvalExprList S_2 Ecaller G F M ps es vs Snext Ef Sargs l ls.
Proof.
  intros S_1 Ecaller G F M ps es vs Snext Ef Sargs l ls H. induction H; intros.
  - (* ExprList nil *)
    constructor. rewrite H0 in H. auto.
  - (* ExprList cons *)
    apply E_ExprList_cons with Snext; auto.
    eapply S_Equal_EvalExpr; eauto.
Qed.


Lemma S_Equal_EvalStmt : forall S_1 E G F M st S',
  EvalStmt S_1 E G F M st S' ->
  forall S_2,
  NatMap.Equal S_1 S_2 ->
  EvalStmt S_2 E G F M st S'.
Proof.
  intros S_1 E G F M st S' H. induction H; intros.
  - (* Skip *)
    constructor. rewrite H0 in H. auto.
Qed.


Lemma E_Equal_EvalExpr : forall S E_1 G F M e v S',
  EvalExpr S E_1 G F M e v S' ->
  forall E_2,
  StringMap.Equal E_1 E_2 ->
  EvalExpr S E_2 G F M e v S'.
Proof.
  apply (EvalExpr_mut
      (* EvalExpr *)
      (fun S E_1 G F M e v S' (h : EvalExpr S E_1 G F M e v S' ) =>
        forall E_2,
        StringMap.Equal E_1 E_2 ->
        EvalExpr S E_2 G F M e v S')
      (* EvalStmt *)
      (fun S E_1 G F M stmt S' (h : EvalStmt S E_1 G F M stmt S' ) =>
        forall E_2,
        StringMap.Equal E_1 E_2 ->
        EvalStmt S E_2 G F M stmt S')
      (* EvalExprList *)
      (fun S Ecaller_1 G F M ps es vs Snext Ef Sargs l ls
        (h : EvalExprList S Ecaller_1 G F M ps es vs Snext Ef Sargs l ls) =>
        forall Ecaller_2,
        StringMap.Equal Ecaller_1 Ecaller_2 ->
        EvalExprList S Ecaller_2 G F M ps es vs Snext Ef Sargs l ls)
    ); intros.
  - (* Num *)
    constructor; auto.
  - (* Local var *)
    apply E_LocalVar with l; auto. rewrite H in m. auto.
  - (* Global var *)
    apply E_GlobalVar with l; auto. rewrite H in n. auto.
  - (* ParenExpr *)
    constructor; auto.
  - (* UnExpr *)
    constructor; auto.
  - (* BinExpr *)
    apply E_BinExpr with S'; auto.
  - (* Local assignment *)
    apply E_Assign_Local with l S'; auto. rewrite H0 in m. auto.
  - (* Global assignment *)
    apply E_Assign_Global with l S'; auto. rewrite H0 in n. auto.
  - (* Function call *)
    apply E_FunctionCall with params fstmt fexpr l ls Ef Sargs S' S'' S''' S'''' vs; auto.
  - (* Macro invocation *)
    apply E_MacroInvocation with params mexpr M' ef; auto.
  - (* Statements *)
    constructor; auto.
  - (* ExprList (nil) *)
    constructor; auto.
  - (* ExprList (cons) *)
    apply E_ExprList_cons with Snext; auto.
Qed.


Lemma E_Equal_EvalStmt : forall S E_1 G F M st S',
  EvalStmt S E_1 G F M st S' ->
  forall E_2,
  StringMap.Equal E_1 E_2 ->
  EvalStmt S E_2 G F M st S'.
Proof.
  intros S_1 E G F M st S' H. induction H; intros.
  - (* Skip *)
    constructor; auto.
Qed.


Lemma EvalExpr_deterministic : forall S E G F M e v1 S'1,
  EvalExpr S E G F M e v1 S'1 ->
  forall v2 S'2,
  EvalExpr S E G F M e v2 S'2 ->
  v1 = v2 /\ NatMap.Equal S'1 S'2.
Proof.
  apply (EvalExpr_mut
      (* EvalExpr *)
      (fun S E G F M e v1 S'1 (h : EvalExpr S E G F M e v1 S'1 ) =>
        forall v2 S'2,
          EvalExpr S E G F M e v2 S'2 ->
          v1 = v2 /\ NatMap.Equal S'1 S'2)
      (* EvalStmt *)
      (fun S E G F M stmt S'1 (h : EvalStmt S E G F M stmt S'1 ) =>
        forall S'2,
          EvalStmt S E G F M stmt S'2 ->
          NatMap.Equal S'1 S'2)
      (* EvalExprList *)
      (fun Sprev Ecaller G F M ps es vs1 Snext1 Ef1 Sargs1 l1 ls1
        (h : EvalExprList Sprev Ecaller G F M ps es vs1 Snext1 Ef1 Sargs1 l1 ls1) =>
        forall vs2 Snext2 Ef2 Sargs2 l2 ls2,
          EvalExprList Sprev Ecaller G F M ps es vs2 Snext2 Ef2 Sargs2 l2 ls2 ->
          vs1 = vs2 /\ NatMap.Equal Snext1 Snext2 /\ StringMap.Equal Ef1 Ef2 /\ NatMap.Equal Sargs1 Sargs2 /\ l1 = l2 /\ ls1 = ls2)
    ); intros; auto.
  - (* Num *)
    inversion_clear H. split; auto.
    rewrite H0 in e. symmetry in e. auto.
  - (* Local Var *)
    inversion_clear H.
    + (* Local *)
      assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst l0.
      assert (v=v2). { eapply NatMapFacts.MapsTo_fun; eauto. }
      subst v2; split; auto. rewrite <- e. auto.
    + (* Global (contradiction *)
      apply StringMap_mapsto_in in m. contradiction.
  - (* Global Var *)
    inversion_clear H.
    + (* Local *)
      apply StringMap_mapsto_in in H1. contradiction.
    + (* Global (contradiction *)
      assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst l0.
      assert (v=v2). { eapply NatMapFacts.MapsTo_fun; eauto. }
      subst v2; split; auto. rewrite <- H0. symmetry. auto.
  - (* ParenExpr *)
    inversion_clear H0; auto.
  - (* UnExpr *)
      inversion_clear H0.
      destruct H with v0 S'2; auto. subst. auto.
  - (* BinExpr *)
    inversion_clear H1.
    (* Left operand*)
    assert (v1 = v3 /\ NatMap.Equal S' S'0). { auto. }
    destruct H1; subst.
    (* Right operand *)
    assert (v2 = v4 /\ NatMap.Equal S'' S'2).
    { apply H0. apply S_Equal_EvalExpr with S'0; auto. symmetry. auto. }
    destruct H1; subst.
    auto.
  - (* Local Assignment *)
    inversion_clear H0.
    + (* Local assignment *)
      assert (v = v2 /\ NatMap.Equal S' S'0). { auto. }
      destruct H0. subst v2.
      assert (l0 = l). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst. rewrite <- H3 in e1. auto.
    + (* Global assignment (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
  - (* Global Assignment *)
    inversion_clear H0.
    + (* Local assignment (contradiction) *)
      apply StringMap_mapsto_in in H1. contradiction.
    + (* Global assignment *)
      assert (v = v2 /\ NatMap.Equal S' S'0). { auto. }
      destruct H0. subst v2.
      assert (l0 = l). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst. auto. rewrite <- H4 in e1. auto.
  - (* Function call *)
    inversion_clear H2.
    + (* Function call *)
      assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
      { eapply StringMapFacts.MapsTo_fun; eauto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      assert (vs = vs0 /\ NatMap.Equal S' S'0 /\ StringMap.Equal Ef Ef0 /\ NatMap.Equal Sargs Sargs0 /\ l = l0 /\ ls = ls0). { auto. }
      destruct H2. destruct H14. destruct H15. destruct H16. destruct H17. subst vs0 l0 ls0.
      assert (NatMap.Equal S'' S''0).
      { rewrite <- H14 in H10. rewrite <- H16 in H10. rewrite <- e2 in H10. symmetry. auto. }
      assert (NatMap.Equal S''' S'''0). symmetry in H2. symmetry in H15.
      { apply S_Equal_EvalStmt with (S_2:=S'') in H11; auto.
        apply E_Equal_EvalStmt with (E_2:=Ef) in H11; auto. }
      assert (v = v2 /\ NatMap.Equal S'''' S''''0).
      symmetry in H17. symmetry in H15.
      { apply S_Equal_EvalExpr with (S_2:=S''') in H12; auto. 
        apply E_Equal_EvalExpr with (E_2:=Ef) in H12; auto. }
      destruct H18. subst v2. rewrite H19 in e5.
      rewrite <- e5 in H13. symmetry in H13. auto.
    + (* Macro invocation (contradiction) *)
      apply StringMap_mapsto_in in H3. contradiction.
  - (* Macro invocation *)
    inversion_clear H0.
    + (* Function call (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
    + (* Macro invocation *)
      assert ((params0, mexpr0) = (params, mexpr)).
      { eapply StringMapFacts.MapsTo_fun; eauto. }
      inversion H0. subst params0 mexpr0. clear H0.
      assert (ef = ef0).
      { eapply MacroSubst_deterministic; eauto. }
      subst ef0.
      assert (M' = M'0). { rewrite e, H2. reflexivity. }
      subst M'0. apply H; auto. rewrite H0. auto.
  - (* Statements *)
    inversion_clear H. rewrite e in H0. auto.
  - (* EvalExprList nil *)
    inversion_clear H. rewrite e in H0. repeat (split; auto; try reflexivity).

  - (* EvalExprList cons *)
    inversion_clear H1.
    assert (v = v0 /\ NatMap.Equal Snext Snext0). { auto. }
    destruct H1. subst v0.
    assert (vs = vs0 /\ NatMap.Equal Sfinal Snext2 /\ StringMap.Equal Ef' Ef'0 /\ NatMap.Equal Sargs' Sargs'0 /\ l = l2 /\ ls = ls0).
    { symmetry in H7. apply S_Equal_EvalExprList with (S_2:=Snext) in H3; auto. }
    destruct H1. destruct H8. destruct H9. destruct H10. destruct H11. subst.
    split; auto. split; auto.
    split. rewrite H9. reflexivity.
    split. rewrite H10. reflexivity.
    auto.
Qed.









