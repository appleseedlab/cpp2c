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


(* The following lemmas involve all parts of program evaluation
   (e.g., expression, argument list, and statement evaluation).
   Coq's built-in induction tactic is not powerful enough to provide
   us with the induction hypotheses necessary to prove these lemmas, so
   we must define our own induction schema for these proofs *)
Scheme EvalExpr_mut := Induction for EvalExpr Sort Prop
with EvalStmt_mut := Induction for EvalStmt Sort Prop
with EvalArgs_mut := Induction for EvalArgs Sort Prop.


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
  intros. induction H; try constructor. Qed.


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
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalArgs Sprev Ecaller G (StringMap.add x fdef F) M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply EvalArgs_cons with Snext; auto.
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
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.update F F') M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
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
  - apply EvalArgs_cons with Snext; auto.
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
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.diff F F') M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with
      params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
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
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma EvalArgs_notin_F_add_EvalArgs : forall S E G F M ps es vs S' Ef Sargs l,
  EvalArgs S E G F M ps es vs S' Ef Sargs l->
  forall x fdef,
    ~ StringMap.In x F ->
    EvalArgs S E G (StringMap.add x fdef F) M ps es vs S' Ef Sargs l.
Proof.
  apply (
    EvalArgs_mut
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
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall x fdef,
        ~ StringMap.In x F ->
        EvalArgs Sprev Ecaller G (StringMap.add x fdef F) M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
    + apply StringMapFacts.add_mapsto_iff. right. split.
      * unfold not; intros. subst. apply StringMap_mapsto_in in m.
        contradiction.
      * auto.
  - apply E_MacroInvocation with params mexpr M' ef; auto.
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma EvalArgs_Disjoint_update_F_EvalArgs : forall S E G F M ps es vs S' Ef Sargs l,
  EvalArgs S E G F M ps es vs S' Ef Sargs l ->
  forall F',
    StringMapProperties.Disjoint F F' ->
    EvalArgs S E G (StringMapProperties.update F F') M ps es vs S' Ef Sargs l.
Proof.
  apply (
    EvalArgs_mut
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
      (* EvalArgs *)
      (fun Sprev Ecaller G F M ps es vs Snext Ef Sargs l
      (h : EvalArgs Sprev Ecaller G F M ps es vs Snext Ef Sargs l) =>
        forall F',
          StringMapProperties.Disjoint F F' ->
          EvalArgs Sprev Ecaller G (StringMapProperties.update F F') M ps es vs Snext Ef Sargs l)
    ); intros; try constructor; auto.
  - apply E_LocalVar with l; auto.
  - apply E_GlobalVar with l; auto.
  - apply E_BinExpr with S'; auto.
  - apply E_Assign_Local with l S'; auto.
  - apply E_Assign_Global with l S'; auto.
  - apply E_FunctionCall with params fstmt fexpr ls Ef Sargs S' S'' S''' S'''' vs l; auto.
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
  - apply EvalArgs_cons with Snext; auto.
Qed.


Lemma EvalExpr_Var_x_in_E_or_G : forall S E G F M x v S',
  EvalExpr S E G F M (Var x) v S' ->
  StringMap.In x E \/ StringMap.In x G.
Proof.
  intros. inversion_clear H.
  - left. apply StringMap_mapsto_in in H0. auto.
  - right. apply StringMap_mapsto_in in H1. auto.
Qed.