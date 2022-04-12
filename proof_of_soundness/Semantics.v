(*  Semantics.v
    Definition of the big-step operational semantics for the language
    as a relation, definition of macro substitution as relations, and lemmas
    concerning these relations.
*)

Require Import
Coq.Lists.List
  Coq.Logic.Classical_Prop
  Coq.Strings.String
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  ConfigVars
  MapLemmas
  Syntax.


(*  Right now, a term that fails to evaluate will simply get "stuck";
    i.e. it will fail to be reduced further. *)
Inductive EvalExpr:
  store -> environment -> environment ->
  function_table -> macro_table ->
  expr ->
  Z -> store -> Prop :=
  (*  Numerals evaluate to their integer representation and do not
      change the store *)
  | E_Num : forall S E G F M z S',
    NatMap.Equal S' S ->
    EvalExpr S E G F M (Num z) z S'
  (*  Local variable lookup *)
  | E_LocalVar : forall S E G F M x l e v S',
    (*  Variable is found in local environment *)
    StringMap.MapsTo x l E ->
    (*  L-value maps to an R-value *)
    NatMap.MapsTo l e S ->
    (*  Evaluate that R-value *)
    EvalExpr S E G F M e v S' ->
    EvalExpr S E G F M (Var x) v S'
  (*  Global variable lookup *)
  | E_GlobalVar : forall S E G F M x l e v S',
    (*  Local variables shadow global variables, so only if a local
        variable lookup fails do we check the global environment. *)
    ~ StringMap.In x E->
    (*  Variable is found in global environment *)
    StringMap.MapsTo x l G ->
    (*  L-value maps to R-value *)
    NatMap.MapsTo l e S ->
    (*  Evaluate that R-value *)
    EvalExpr S E G F M e v S' ->
    EvalExpr S E G F M (Var x) v S'
  (*  Parenthesized expressions evaluate to themselves. *)
  | E_ParenExpr : forall S E G F M e0 v S',
    (*  Evaluate the inner expression *)
    EvalExpr S E G F M e0 v S' ->
    EvalExpr S E G F M (ParenExpr e0) v S'
  (*  Unary expressions *)
  | E_UnExpr : forall S E G F M S' uo e0 v,
    (*  Evaluate the inner expression *)
    EvalExpr S E G F M e0 v S' ->
    (*  Perform the unary operations on the value obtained *)
    EvalExpr S E G F M (UnExpr uo e0) ((unop_to_op uo) v) S'
  (*  Binary expressions. Left operands are evaluated first. *)
  (*  NOTE: Evaluation rules do not handle operator precedence.
      The parser must use a concrete syntax to generate a parse tree
      with the appropriate precedence levels in it. *)
  | E_BinExpr : forall S E G F M bo e1 e2 v1 v2 S' S'',
    (*  Evaluate the left operand *)
    EvalExpr S E G F M e1 v1 S' ->
    (*  Evaluate the right operand *)
    EvalExpr S' E G F M e2 v2 S'' ->
    (*  Perform the binary operation on the values obtained *)
    EvalExpr S E G F M (BinExpr bo e1 e2) ((binop_to_op bo) v1 v2) S''
  (*  Variable assignments update the store by adding a new L-value to
      R-value mapping or by overriding an existing one.
      The R-value is returned along with the updated state. *)
  (*  Local variable assignment overrides global variable assignment. *)
  | E_Assign_Local : forall S E G F M l x e z S',
    (*  Find the variable in the local environment *)
    StringMap.MapsTo x l E ->
    (*  Evaluate the RHS of the assignment *)
    EvalExpr S E G F M e z S' ->
    (*  Add the new mapping to the store *)
    NatMap.MapsTo l (Num z) S' ->
    EvalExpr S E G F M (Assign x e) z S'
  (*  Global variable assignment *)
  | E_Assign_Global : forall S E G F M l x e z S',
    (*  The variable is not found in the local environment *)
    ~ StringMap.In x E ->
    (*  Find the variable in the global environment *)
    StringMap.MapsTo x l G ->
    (*  Evaluate the RHS of the assignment *)
    EvalExpr S E G F M e z S' ->
    (*  Add the new mapping to the store *)
    NatMap.MapsTo l (Num z) S' ->
    EvalExpr S E G F M (Assign x e) z S'
  (*  For function calls, we perform the following steps:
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
           Ef Sf es' S' S'' S''' S'''' S''''' v,
    (*  Macro definitions shadow function definitions, so function calls
        only occur if a macro definition is not found *)
    ~ StringMap.In x M ->

    (*  Function name maps to some function *)
    StringMap.MapsTo x (params, fstmt, fexpr) F ->

    (*  Deterministically create L-values *)
    ls = seq ((NatMap.cardinal S) + 1) (List.length es)%list ->

    (*  Deterministically create Ef and Sargs *)
    StringMap.Equal Ef (StringMapProperties.of_list (combine params ls)) ->

    (*  Evaluate the function's arguments, then create the argument store *)
    EvalExprList S E G F M es S' es' ->
    NatMap.Equal Sf (NatMapProperties.of_list (combine ls es')) ->

    (*  All the L-values used in the argument store do not appear
        in the original store. *)
    NatMapProperties.Partition S'' S' Sf ->
    NatMap.Equal S'' (NatMapProperties.update S' Sf) ->

    (*  Evaluate the function's body under the caller's environment *)
    EvalStmt S'' Ef G F M fstmt S''' ->
    EvalExpr S''' Ef G F M fexpr v S'''' ->

    (*  Only keep in the store the L-value mappings that were there when
        the function was called; i.e., remove from the store all mappings
        whose L-value is in Ef/Sargs. *)
    NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
    (forall l e, NatMap.MapsTo l e S''''' <-> NatMap.In l S' ) ->

    EvalExpr S E G F M (CallOrInvocation x es) v S'''''
  (*  Macro invocation *)
  (*  Mostly the same as function call, with a few key differences
      1) Macros are found in the macro table
      2) Macro definitions do not contain a statement
      3) Macro argument store is not evaluated
      4) Macro argument environment is unioned with the caller environment *)
  (*  Macro definitions shadow function definitions *)
  | E_MacroInvocation :
    forall S E G F M x es params mexpr ls
           Em E' Sm S' S'' S''' v,
    StringMap.MapsTo x (params, mexpr) M ->

    (*  Deterministically create L-values *)
    ls = seq ((NatMap.cardinal S) + 1) (List.length es)%list ->

    (*  Deterministically create Ef and Sargs *)
    StringMap.Equal Em (StringMapProperties.of_list (combine params ls)) ->

    (*  Create the argument store *)
    NatMap.Equal Sm (NatMapProperties.of_list (combine ls es)) ->

    (*  All the L-values used in the argument store do not appear
        in the original store. *)
    NatMapProperties.Partition S' S Sm ->
    NatMap.Equal S' (NatMapProperties.update S Sm) ->

    (*  Evaluate the macro's body under the caller's environment *)
    StringMap.Equal E' (StringMapProperties.update E Em) ->
    EvalExpr S' E' G F M mexpr v S'' ->

    (*  Only keep in the store the L-value mappings that were there when
        the macro was called; i.e., remove from the store all mappings
        whose L-value is in Ef/Sargs. *)
    NatMap.Equal S''' (NatMapProperties.restrict S'' S) ->
    (forall l e, NatMap.MapsTo l e S''' <-> NatMap.In l S ) ->

    EvalExpr S E G F M (CallOrInvocation x es) v S'''
with EvalStmt :
  store -> environment -> environment ->
  function_table -> macro_table ->
  stmt ->
  store -> Prop :=
  (*  A skip statement does not change the state *)
  | E_Skip : forall S E G F M S',
    NatMap.Equal S' S ->
    EvalStmt S E G F M Skip S'
(*  Evaluates all the expressions in a store.
    Returns the original store after all side-effects of the values in
    the argument store's expressions have been evaluated, and the simplified
    argument store in which all expressions have been converted to their
    numeral forms.
    We don't ever work with the internals of this; this definition is here
    mainly just here so the proof will work. *)
with EvalExprList :
  store -> environment -> environment ->
  function_table -> macro_table ->
  list expr -> (* The store to evaluate *)
  store -> list expr -> Prop :=
  | E_ExprList_nil : forall S E G F M S',
    NatMap.Equal S' S ->
    EvalExprList S E G F M nil S' nil
  | E_ExprList_cons : forall S E G F M e es z es' S' S'',
    (*  Evaluate the current element *)
    EvalExpr S E G F M e z S' ->
    (*  Evaluate the rest of the store *)
    EvalExprList S' E G F M es S'' es' ->
    EvalExprList S E G F M (e::es) S'' ((Num z)::es').


(*  The following lemmas involve all parts of program evaluation
    (e.g., expression, argument list, and statement evaluation).
    Coq's built-in induction tactic is not powerful enough to provide
    us with the induction hypotheses necessary to prove these lemmas, so
    we must define our own induction schema for these proofs *)
Scheme EvalExpr_Scheme := Induction for EvalExpr Sort Prop
with EvalStmt_Scheme := Induction for EvalStmt Sort Prop
with EvalExprList_Scheme := Induction for EvalExprList Sort Prop.


(*  If an expression e terminates under some context with an initial store S,
    and some other store S2 is equal to S, then e will also terminate
    under the original context where S has been replaced with S2 *)
Lemma S_Equal_EvalExpr : forall S1 E G F M e z S',
  EvalExpr S1 E G F M e z S' ->
  forall S2,
  NatMap.Equal S1 S2 ->
  EvalExpr S2 E G F M e z S'.
Proof.
  apply (EvalExpr_Scheme
    (fun S1 E G F M e z S' (h : EvalExpr S1 E G F M e z S') =>
      forall S2,
      NatMap.Equal S1 S2 ->
      EvalExpr S2 E G F M e z S'
    )
    (fun S1 E G F M s S' (h : EvalStmt S1 E G F M s S') =>
      forall S2,
      NatMap.Equal S1 S2 ->
      EvalStmt S2 E G F M s S'
    )
    (fun S1 E G F M es S' es' (h : EvalExprList S1 E G F M es S' es') =>
      forall S2,
      NatMap.Equal S1 S2 ->
      EvalExprList S2 E G F M es S' es'
    )
  ); intros;
      (*  Simple inductive cases *)
      try ( solve [econstructor; eauto] );
      (*  Base cases *)
      try ( solve [econstructor; transitivity S; eauto] ).

  - (*  Local variable *)
    rewrite H0 in *; eapply E_LocalVar; eauto.
  - (*  Global variable *)
    rewrite H0 in *; eapply E_GlobalVar; eauto.
  -
    subst.
    rewrite H2 in *.
    eapply E_FunctionCall; eauto.
  -
    rewrite H0 in *.
    apply E_MacroInvocation with params mexpr ls Em E' Sm S' S''; auto.
    split; intros.
    +
      apply i in H1. rewrite <- H0. assumption.
    +
      apply i. rewrite H0. assumption.
Qed.


Lemma S_Equal_EvalStmt : forall S1 E G F M s S',
  EvalStmt S1 E G F M s S' ->
  forall S2,
  NatMap.Equal S1 S2 ->
  EvalStmt S2 E G F M s S'.
Proof.
  intros.
  induction H.
  -
    constructor.
    rewrite H; auto.
Qed.


Lemma S_Equal_EvalExprList : forall S1 E G F M es S' es',
  EvalExprList S1 E G F M es S' es' ->
  forall S2,
  NatMap.Equal S1 S2 ->
  EvalExprList S2 E G F M es S' es'.
Proof.
  intros.
  induction H.
  -
    constructor.
    rewrite H; auto.
  -
    constructor 2 with (S':=S'); eauto using S_Equal_EvalExpr.
Qed.


Lemma E_Equal_EvalExpr : forall S E1 G F M e z S',
  EvalExpr S E1 G F M e z S' ->
  forall E2,
  StringMap.Equal E1 E2 ->
  EvalExpr S E2 G F M e z S'.
Proof.
  apply (EvalExpr_Scheme
    (fun S E1 G F M e z S' (h : EvalExpr S E1 G F M e z S') =>
      forall E2,
      StringMap.Equal E1 E2 ->
      EvalExpr S E2 G F M e z S'
    )
    (fun S E1 G F M s S' (h : EvalStmt S E1 G F M s S') =>
      forall E2,
      StringMap.Equal E1 E2 ->
      EvalStmt S E2 G F M s S'
    )
    (fun S E1 G F M es S' es' (h : EvalExprList S E1 G F M es S' es') =>
      forall E2,
      StringMap.Equal E1 E2 ->
      EvalExprList S E2 G F M es S' es'
    )
  ); intros;
      (*  Simple inductive cases *)
      try ( solve [econstructor; eauto] ).

  -
    rewrite H0 in m.
    eapply E_LocalVar; eauto.
  -
    rewrite H0 in n.
    eapply E_GlobalVar; eauto.
  -
    rewrite H0 in m.
    eapply E_Assign_Local; eauto.
  -
    rewrite H0 in n.
    eapply E_Assign_Global; eauto.
  -
    eapply E_MacroInvocation; eauto.
    rewrite <- H0. auto.
Qed.


Lemma E_Equal_EvalStmt : forall S E1 G F M s S',
  EvalStmt S E1 G F M s S' ->
  forall E2,
  StringMap.Equal E1 E2 ->
  EvalStmt S E2 G F M s S'.
Proof.
  intros.
  induction H.
  -
    constructor; auto.
Qed.

Lemma EvalExpr_deterministic : forall S E G F M e z1 S'1,
  EvalExpr S E G F M e z1 S'1 ->
  forall z2 S'2,
  EvalExpr S E G F M e z2 S'2 ->
  z1 = z2 /\ NatMap.Equal S'1 S'2.
Proof.
  apply (EvalExpr_Scheme
    (fun S E G F M e z1 S'1 (h : EvalExpr S E G F M e z1 S'1) =>
      forall z2 S'2,
      EvalExpr S E G F M e z2 S'2 ->
      z1 = z2 /\ NatMap.Equal S'1 S'2
    )
    (fun S E G F M s S'1 (h : EvalStmt S E G F M s S'1) =>
      forall S'2,
      EvalStmt S E G F M s S'2 ->
      NatMap.Equal S'1 S'2
    )
    (fun S E G F M es S'1 es'1 (h : EvalExprList S E G F M es S'1 es'1) =>
      forall S'2 es'2,
      EvalExprList S E G F M es S'2 es'2 ->
      NatMap.Equal S'1 S'2 /\ es'1 = es'2
    )
  ); intros.

  -
    inversion_clear H; split; eauto; transitivity S; auto; symmetry; auto.
  -
    inversion H0; subst.
    +
      apply StringMapFacts.MapsTo_fun with (e:=l0) in m; auto.
      subst l0.
      apply NatMapFacts.MapsTo_fun with (e:=e1) in m0; auto.
      subst e1.
      auto.
    +
      apply StringMap_mapsto_in in m. contradiction.
  -
    inversion H0; subst.
    +
      apply StringMap_mapsto_in in H2. contradiction.
    +
      apply StringMapFacts.MapsTo_fun with (e:=l0) in m; auto.
      subst l0.
      apply NatMapFacts.MapsTo_fun with (e:=e1) in m0; auto.
      subst e1.
      auto.
  -
    inversion_clear H0; auto.
  -
    inversion_clear H0.
    apply H in H1.
    destruct H1.
    subst.
    auto.
  -
    inversion H1; subst.
    apply H in H12.
    destruct H12.
    subst.
    apply S_Equal_EvalExpr with (S2:=S') in H13. 2 : { symmetry; auto. }
    apply H0 in H13.
    destruct H13.
    subst.
    rewrite H4.
    split; reflexivity.
  -
    inversion H0; subst.
    +
      apply StringMapFacts.MapsTo_fun with (e:=l0) in m; auto.
    +
      apply StringMap_mapsto_in in m. contradiction.
  -
    inversion H0; subst.
    +
      apply StringMap_mapsto_in in H3. contradiction.
    +
      apply StringMapFacts.MapsTo_fun with (e:=l0) in m; auto.
  -
    inversion H2.
    +
      subst S0 E0 G0 F0 M0 x0 es0 v0 S'''''0.

      (*  We find the same function *)
      eapply StringMapFacts.MapsTo_fun in m; eauto.
      inversion m; subst params0 fstmt0 fexpr0; clear m.

      (*  L-values are the same *)
      assert (ls = ls0). { subst. auto. }
      subst ls0.

      (*  Argument evaluation is the same *)
      apply H in H9.
      destruct H9.
      subst es'0.

      (*  Updated environments for function evaluation are the same *)
      assert (StringMap.Equal Ef Ef0).
      { subst. rewrite e0. rewrite H8. reflexivity. }

      (*  Updated stores for function evaluation are the same *)
      assert (NatMap.Equal S'' S''0).
      { subst. rewrite e3. rewrite H12. rewrite H4.
        rewrite e2. rewrite H10. reflexivity. }

      (*  Statement evaluation is the same *)
      apply S_Equal_EvalStmt with (S2:=S'') in H13. 2 : { symmetry; auto. }
      apply E_Equal_EvalStmt with (E2:=Ef) in H13. 2 : { symmetry; auto. }
      apply H0 in H13.

      (*  Return expression evaluation is the same *)
      apply S_Equal_EvalExpr with (S2:=S''') in H14. 2 : { symmetry; auto. }
      apply E_Equal_EvalExpr with (E2:=Ef) in H14. 2 : { symmetry; auto. }
      apply H1 in H14; auto.
      destruct H14.
      subst v.
      split; auto.

      (*  Final stores are the same *)
      rewrite H20. rewrite <- H15. auto.
    +
      apply StringMap_mapsto_in in H5. contradiction.
  -
    inversion H0.
    +
      apply StringMap_mapsto_in in m. contradiction.
    +
      subst S0 E0 G0 F0 M0 x0 es0 v0 S'''0.

      (*  We find the same macro *)
      eapply StringMapFacts.MapsTo_fun in m; eauto.
      inversion m; subst params0 mexpr0; clear m.

      (*  L-values are the same *)
      assert (ls = ls0). { subst. auto. }
      subst ls0.

      (*  Updated environments for function evaluation are the same *)
      assert (StringMap.Equal E' E'0).
      { subst. rewrite e3. rewrite H9.
        rewrite e0. rewrite H5. reflexivity. }

      (*  Updated stores for macro evaluation are the same *)
      assert (NatMap.Equal S' S'0).
      { subst. rewrite e2. rewrite H8. rewrite H6.
        rewrite e1. reflexivity. }

      (*  Return expression evaluation is the same *)
      apply S_Equal_EvalExpr with (S2:=S') in H10. 2 : { symmetry; auto. }
      apply E_Equal_EvalExpr with (E2:=E') in H10. 2 : { symmetry; auto. }
      apply H in H10; auto.
      destruct H10.
      subst v.
      split; auto.

      (*  Final stores are the same *)
      rewrite e5. rewrite H16. rewrite H11. reflexivity.
  -
    inversion_clear H.
    transitivity S; auto.
    symmetry; auto.
  -
    inversion_clear H.
    split; auto.
    transitivity S; auto.
    symmetry; auto.
  -
    inversion_clear H1.
    apply H in H2.
    destruct H2.
    subst.

    apply S_Equal_EvalExprList with (S2 := S') in H3. 2: { symmetry; auto. }
    apply H0 in H3.
    destruct H3.
    subst.
    split; auto.
Qed.

