Require Import
  Coq.FSets.FMapList
  Coq.Logic.Classical_Prop
  Coq.Lists.List
  Coq.Strings.String
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  MapTheorems
  EvalRules
  SideEffects
  NoCallsFromFunctionTable
  NoMacroInvocations
  NoVarsInEnvironment
  Transformations.



Lemma no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil :
  forall mexpr,
  (* The macro body must not have side-effects *)
  ~ ExprHasSideEffects mexpr ->
  forall F M,
  (* The macro must not contain a macro invocation *)
  ExprNoMacroInvocations mexpr F M->
  forall Ecaller,
  (* The macro body must not rely on variables from the caller's scope.
     Global variables, however, are allowed. *)
  ExprNoVarsInEnvironment mexpr Ecaller ->
  forall ef,
  MacroSubst nil nil mexpr ef ->
  forall S G v S''',
  EvalExpr S Ecaller G F M ef v S''' ->
  forall S' Ef Sargs l,
  EvalArgs S Ecaller G F M nil nil nil S' Ef Sargs l ->
  (* We will prove that S = S' since there are no side-effects.
     S' and Sargs must be distinct so that we don't overwrite pre-existing
     L-values *)
  NatMapProperties.Disjoint S' Sargs ->
  forall v0 S'''0,
  EvalExpr (NatMapProperties.update S' Sargs) Ef G F M mexpr v0 S'''0 ->
  v = v0.
Proof.
  intros.
  assert ((NatMapProperties.update S' Sargs) = S'''0).
  { apply not_ExprHasSideEffects_S_eq in H6; auto. }
  rewrite H7 in *.
  inversion H2; subst. clear H2.
  inversion H4; subst. clear H4.
  generalize dependent v0. 
  induction H3; intros; try (simpl in H; contradiction).
  -
    inversion H6; auto.
  -
    apply StringMap_mapsto_in in H2. inversion_clear H1.
    contradiction.
  -
    inversion_clear H6.
    + apply StringMapFacts.empty_mapsto_iff in H7. destruct H7.
    + assert (l = l0). { apply StringMapFacts.MapsTo_fun with G x; auto. }
      subst l0. apply NatMapProperties.update_mapsto_iff in H9. destruct H9.
      * apply NatMapFacts.empty_mapsto_iff in H6. destruct H6.
      * destruct H6. apply NatMapFacts.MapsTo_fun with S l; auto.
  -
    simpl in H. inversion_clear H0. inversion_clear H1.
    inversion_clear H6. auto.
  -
    simpl in H. inversion_clear H0. inversion_clear H1.
    inversion_clear H6. assert (v = v1). apply IHEvalExpr; auto.
    subst v1; auto.
  -
    simpl in H. apply Classical_Prop.not_or_and in H. destruct H.
    inversion_clear H0. inversion_clear H1. inversion_clear H6.
    assert (S = S'). { apply not_ExprHasSideEffects_S_eq in H3_; auto. }
    assert ((NatMapProperties.update S (NatMap.empty Z)) = S'0).
    { apply not_ExprHasSideEffects_S_eq in H1; auto. }
    subst S'. rewrite H9 in *. clear H9.
    assert (v1 = v3). { apply IHEvalExpr1; auto. }
    assert (v2 = v4). { apply IHEvalExpr2; auto. }
    subst v3 v4; auto.
Qed.


Theorem transform_expr_sound_mut_v_s : forall M F e F' e',
  TransformExpr M F e F' e' ->
  (* The proof will not work if these variables were introduced sooner.
     Doing so would interfere with the induction hypothesis *)
  forall S E G v1 v2 S'1 S'2,
    EvalExpr S E G F M e v1 S'1 ->
    EvalExpr S E G F' M e' v2 S'2 ->
    v1 = v2 /\ S'1 = S'2.
Proof.
  apply (TransformExpr_mut
    (* Induction rule for TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
    forall S E G v1 v2 S'1 S'2,
      EvalExpr S E G F M e v1 S'1 ->
      EvalExpr S E G F' M e' v2 S'2 ->
      v1 = v2 /\ S'1 = S'2)
    (* Induction rule for TransformArgs *)
    (fun M F es F' es' (h : TransformArgs M F es F' es') =>
    forall S Ecaller G ps1 vs1 vs2 S'1 S'2 Ef1 Ef2 Sargs1 Sargs2 l1 l2,
      EvalArgs S Ecaller G F M ps1 es vs1 S'1 Ef1 Sargs1 l1 ->
      EvalArgs S Ecaller G F' M ps1 es' vs2 S'2 Ef2 Sargs2 l2 ->
      l1 = l2 /\ Ef1 = Ef2 /\ Sargs1 = Sargs2 /\ vs1 = vs2 /\ S'1 = S'2)
    (* Induction rule for TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
    forall S E G S'1 S'2,
      EvalStmt S E G F M stmt S'1 ->
      EvalStmt S E G F' M stmt' S'2 ->
      S'1 = S'2
      )); intros; auto.

  - (* Num *)
    inversion H. inversion H0. subst. auto.
  - (* Var *)
    inversion H; subst.
    + (* Untransformed is a local var *)
      inversion H0; subst.
      * (* Transformed is a local var *)
        apply StringMapFacts.find_mapsto_iff in H2, H3.
        rewrite H3 in H2. inversion H2; subst.
        apply NatMapFacts.find_mapsto_iff in H8, H10.
        rewrite H10 in H8. inversion H8. auto.
      * (* Transformed is a global var *)
        apply StringMap_mapsto_in in H2. contradiction.
    + (* Untransformed is a gloval var *)
      inversion H0; subst.
      * (* Transformed is a local var *)
        apply StringMap_mapsto_in in H4. contradiction.
      * (* Transformed is a global var *)
        apply StringMapFacts.find_mapsto_iff in H3, H5.
        rewrite H5 in H3. inversion H3; subst.
        apply NatMapFacts.find_mapsto_iff in H9, H12.
        rewrite H12 in H9. inversion H9. auto.

  - (* ParenExpr *)
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v1 v2 S'1 S'2; auto.

  - (* UnExpr *)
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v v0 S'1 S'2; auto.
    subst. auto.

  - (* BinExpr *)
    inversion_clear H1. inversion_clear H2.
    destruct H with S E G v0 v4 S' S'0; auto.
    { subst F''.
      apply EvalExpr_ExprNoCallsFromFunctionTable_remove_function_EvalExpr in H1; auto. }
    subst S'0 v4. destruct H0 with S' E G v3 v5 S'1 S'2; auto.
    { subst F'.
      apply EvalExpr_ExprNoCallsFromFunctionTable_remove_function_EvalExpr; auto. }
    subst S'2 v5. auto.

  - (* Assign *)
    inversion H0; subst.
    + inversion H1; subst.
      * apply StringMapFacts.find_mapsto_iff in H4, H5.
        rewrite H5 in H4. inversion H4; subst.
        destruct H with S E G v1 v2 S' S'0; auto.
        subst. auto.
      * apply StringMap_mapsto_in in H4. contradiction.
    + inversion H1; subst.
      * apply StringMap_mapsto_in in H6. contradiction.
      * apply StringMapFacts.find_mapsto_iff in H5, H7.
        rewrite H7 in H5. inversion H5; subst.
        destruct H with S E G v1 v2 S' S'0; auto.
        subst. auto.
  - (* Function call *)
    inversion_clear H2. inversion_clear H3.
    +
      assert (StringMap.MapsTo x (params, fstmt', fexpr') F').
      { subst. apply StringMapFacts.add_mapsto_iff. left. auto. }
      apply StringMapFacts.find_mapsto_iff in H15, H3.
      rewrite H3 in H15. inversion H15. clear H15.
      apply StringMapFacts.find_mapsto_iff in m, H5.
      rewrite H5 in m. inversion m.
      subst.
      destruct H with S E G params1 vs vs0 S' S'0 Ef Ef0 Sargs Sargs0 l l0; auto.
      destruct H15. destruct H21. destruct H25. subst.
      destruct H0 with (NatMapProperties.update S'0 Sargs0) Ef0 G S''' S'''0 ; auto.
      destruct H1 with S''' Ef0 G v1 v2 S'''' S''''0; auto. subst.
      apply NatMap_Equal_eq_iff in H14, H24. subst. auto.
    + apply StringMap_mapsto_in in H2. contradiction.
    + apply StringMap_mapsto_in in H4. contradiction.

  - (* Object like macro without side-effects, shared variables with the caller environment,
       or nested macro invocations *)
    inversion H0. inversion H1.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + inversion H1.
      subst S0 E0 G0 F0 M0 x0 es v1 S'1.
      subst S1 E1 G1 F1 M1 x1 es0 v2 S'''''.
      * (* Proof of equivalence *)

        (* Prove that the macro body does not change after transformation *)
        assert (mexpr = mexpr').
        { apply TransformExpr_ExprNoMacroInvocations_e_eq with M F F'; auto. }
        subst mexpr'.

        (* No side-effects in function *)

        (* Prove that the definition that we know the function maps to
           is the same one that we added during the transformation *)
        assert ( (params1, fstmt, fexpr) = (nil, Skip, mexpr) ).
        { apply StringMapFacts.MapsTo_fun with F' fname; auto.
          rewrite e1. apply StringMapFacts.add_mapsto_iff. left. auto. }
        inversion H2. subst params1 fstmt fexpr. clear H2.

        (* Add to the context all the premises we get from evaluating an
           empty argument list *)
        inversion H21. subst Sprev E G0 F0 M0 vs S'0 Ef Sargs l.

        (* Prove that there are no side-effects caused by the skip statement *)
        apply Skip_S_eq in H26. subst S'''.

        (* Prove that there are no side-effects cause by the return expression *)
        assert (S'' = S''''). { apply not_ExprHasSideEffects_S_eq in H32; auto. }
        subst S''''.

        (* Prove that after freeing the memort allocated for function environment,
           the store reverts back to its original state *)
        assert (NatMap.Equal S (NatMapProperties.restrict S'' S)).
        { rewrite H25. apply NatMap_disjoint_restrict_Equal; auto. }
        rewrite <- H2 in H35. apply NatMap_Equal_eq_iff in H35. subst S'2.

        (* No side-effects in macro *)

        (* Prove that the definition that we know the macro maps to
           is the same one we asserted in the transformation *)
        assert ( (params, mexpr) = (params0, mexpr0) ).
        { apply StringMapFacts.MapsTo_fun with M x; auto. }
        inversion H3. subst params0 mexpr0. clear H3.

        (* Prove that after macro substitution, the macro body still
           does not have side-effects *)
        assert (~ ExprHasSideEffects ef).
        { apply not_ExprHasSideEffects_MacroSubst_not_ExprHasSideEffects with mexpr params nil; auto. }

        (* Prove that the macro invocation does not have side-effects *)
        assert (S = S').
        { apply not_ExprHasSideEffects_S_eq in H15; auto; auto. }
        subst S'.

        (* Use one of our premises to assert that the macro does not contain
           variables from the caller environment *)
        (* NOTE: We should probably add the environment to the transformation
           relation so that we don't have to use such a generous premise *)
        assert (ExprNoVarsInEnvironment mexpr Ecaller).
        { apply e0 with S G v S; auto. }
        split.
        --
          (* Prove that the expression will result in the same value
             under call-by-name and call-by-value *)
          apply no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil with
            mexpr F' M' Ecaller mexpr S G S S (StringMap.empty nat) (NatMap.empty Z) 0 S'';
              auto.
            ++ (* Prove that the macro body does contain a macro invocation *)
               subst M'. apply ExprNoMacroInvocations_remove_ExprNoMacroInvocations.
               apply TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations with F mexpr; auto.
            ++ constructor.
            ++ (* Prove that macro expression evaluation works the same
                  under an updated function table *)
               inversion H12. subst ef mexpr0 params.
               subst F'. apply EvalExpr_notin_F_add_EvalExpr; auto.
            ++ constructor.
            ++ (* Prove that function expression evaluation works the same
                  under an updated macro table *)
               subst S'' M'. apply ExprNoMacroInvocations_remove_EvalExpr; auto.
               apply TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations with F mexpr; auto.
        -- auto.
      * apply StringMap_mapsto_in in H18. contradiction.
  - inversion H. inversion H0. subst. split; auto.
  - inversion H1. inversion H2.
    destruct H with S Ecaller G v v0 Snext Snext0; auto. subst. inversion H31. subst.
    destruct H0 with Snext0 Ecaller G ps vs vs0 S'1 S'2 Ef' Ef'0 Sargs' Sargs'0 l l0; auto.
    destruct H4. destruct H8. destruct H9. subst.
    split; auto.
  - inversion H. inversion H0. subst. auto.
Qed.


(* Issues:
           1) Proving evaluation equivalence under call-by-name and call-by-value
           2) Coq doesn't treat FMap.Equal as the same thing as Logic.eq

           Solutions:
           1) ???
           2) Just use an axiom stating that Equal implies eq. *) 
