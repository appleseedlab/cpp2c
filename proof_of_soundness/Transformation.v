(*  Transformation.v
    Definition of the transformation that Cpp2C performs as well as some
    functions that it uses
*)

Require Import
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  Semantics
  MapLemmas.

(*
  Notes

  We may not need to map L-values to expressions if we can assume that
  the macro body does not capture variables from its caller
  environment.

  We should try and fix the issue with macro recursion.
*)


(*  An expression list without side-effects is one which does
    not modify its input store when evaluated *)
Definition ExprListNoSideEffects (es : list expr) :=
  forall S E G F M S' es',
  EvalExprList S E G F M es S' es' ->
  NatMap.Equal S S'.


(*  Relation only holds if an expression does not reference any function in the
    given function table *)
Definition ExprDoesNotCall (e : expr) (x : string) :=
  forall S E G F M v S' fdef,
  EvalExpr S E G F M e v S' <->
  EvalExpr S E G (StringMap.add x fdef F) M e v S'.


(*  Relation only holds if an expression does not reference any function in the
    given function table *)
Definition ExprListDoesNotCall (es : list expr) (x : string) :=
  forall S E G F M S' es' fdef,
  EvalExprList S E G F M es S' es' <->
  EvalExprList S E G (StringMap.add x fdef F) M es S' es'.


(*  Relation only holds if an expression can be evaluated under a subset of
    an environment it is evaluated under *)
Definition ExprDoesNotCaptureVars (e : expr) (E : environment) :=
  forall S G F M z S' E',
  EvalExpr S (StringMapProperties.update E E') G F M e z S' ->
  EvalExpr S E' G F M e z S'.


(*  Relation only holds if evaluation under two stores reutrn the same
    R-value *)
Definition RValueEquivalent
  (S1: store) (S2: store) :=
  forall E G F M e z1 S'1,
  EvalExpr S1 E G F M e z1 S'1 ->
  forall z2 S'2,
  EvalExpr S2 E G F M e z2 S'2 ->
  z1 = z2.

(*  Corollary:
    If a list of expressions do not have side-effects,
    then a store created from the raw expressions
    and the store created from the evaluated expressions
    are R-value equivalent *)


Theorem Transformation_Sound :
  forall x params mexpr M,
  (*  We are transforming a macro *)
  StringMap.MapsTo x (params, mexpr) M ->

  forall es,
  (*  The macro arguments do not have side-effects *)
  ExprListNoSideEffects es ->

  forall S E G F z1 S'1,
  (*  The original macro invocation terminates *)
  EvalExpr S E G F M (CallOrInvocation x es) z1 S'1 ->

  (*  The original expression does not capture variables from its caller
      environment *)
    ExprDoesNotCaptureVars mexpr E ->

  (*  Evaluation under the macro environment and store results in the same
      return value as under the function environment and store *)
  ( forall S' es' ls,
    EvalExprList S E G F M es S' es' ->
    RValueEquivalent
      (NatMapProperties.update S (NatMapProperties.of_list (combine ls es)))        (* Sm *)
      (NatMapProperties.update S' (NatMapProperties.of_list (combine ls es')))       (* Sf *)
  ) ->


  forall x',
  (*  The newly defined function is not in the function table *)
  ~ StringMap.In x' F ->
  (*  The newly defined function is not in the macro table *)
  ~ StringMap.In x' M ->
  (*  The original macro body does not call the newly defined function *)
  (*  We could probably prove this, since if the macro body did call the
      newly defined function, it would not terminate *)
  ExprDoesNotCall mexpr x' ->
  ExprListDoesNotCall es x' ->

  forall z2 S'2,
  (*  The transformed function call terminates *)
  EvalExpr S E G (StringMap.add x' (params, Skip, mexpr) F) M (CallOrInvocation x' es) z2 S'2 ->

  z1 = z2 /\ NatMap.Equal S'1 S'2.
Proof.
  intros
    x params mexpr M MacroFound es NoSideEffectsInParams
    S E G F z1 S'1 MacroInvocation NoEnvironmentCapture
    RValueEquivalence x' x'NotInFunctionTable x'NotInMacroTable
    mexprDoesNotCallx' esDoNoCallx' z2 S'2 FunctionCall.

  inversion MacroInvocation; subst.
  - (*  Original expression is a function call (contradiction) *)
    apply StringMap_mapsto_in in MacroFound.
    contradiction.
  - (*  Original expression is a macro invocation *)

    (*  Original macro maps to the definition we said it did *)
    eapply StringMapFacts.MapsTo_fun in MacroFound; eauto.
    inversion MacroFound; subst params0 mexpr0; clear MacroFound.
    clear H1.
    inversion FunctionCall; subst.
    + (*  Transformed expression is a function call (transformation) *)

      (*  Transformed function maps to the one we added to the function table *)
      apply StringMapFacts.add_mapsto_iff in H2.
      destruct H2. 2: { destruct H. contradiction. }
      destruct H.
      inversion H0; subst params0 fstmt fexpr; clear H0.
      clear H.

      (*  Evaluating the function call's arguments does not change the store *)
      assert (NatMap.Equal S S'0).
      { apply NoSideEffectsInParams in H11; auto. }

      (*  Macro environment = function environment *)
      assert (StringMap.Equal Em Ef). { rewrite H3, H10. reflexivity. }
      clear H3 H10.

    (*  Evaluating the function body (Skip) does not change the store *)
    inversion_clear H16.

    (*  Evaulating the function body is the same as evaluating the macro body *)
    move H8 after H0.
    move H18 after H8.
    apply mexprDoesNotCallx' in H18.
    apply E_Equal_EvalExpr with (E2:=(StringMapProperties.update E Em)) in H8; auto.
    apply E_Equal_EvalExpr with (E2:=Em) in H18. 2 : { symmetry; auto. }
    apply NoEnvironmentCapture in H8.

    apply S_Equal_EvalExpr with (S2:=(NatMapProperties.update S (NatMapProperties.of_list (combine (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)) es)))) in H8.
    2:  { rewrite H6.
          rewrite H4.
          reflexivity. }

    apply S_Equal_EvalExpr with (S2:=(NatMapProperties.update S'0 (NatMapProperties.of_list (combine (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)) es')))) in H18.
    2:  { rewrite H2.
          rewrite H15.
          rewrite <- H.
          rewrite H12.
          reflexivity. }
    unfold RValueEquivalent in RValueEquivalence.
    apply RValueEquivalence
      with (S':=S'0) (z1:=z1) (S'1:=S'')
      in H18; auto.
    2 : { apply esDoNoCallx' in H11; auto. }

    subst.
    split.
    *
      (*  Final values are the same *)
      reflexivity.
    *
      (*  Final stores are the same *)
      apply NatMapFacts.Equal_mapsto_iff.
      intros.
      rewrite H17.
      rewrite H27. rewrite <- H.
      tauto.
    + (* Transformed expression is a macro invocation (contradiction) *)
      apply StringMap_mapsto_in in H1.
      contradiction.
Qed.

