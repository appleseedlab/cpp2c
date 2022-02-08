(*  Theorems.v
    Contains theorems directly concerning the soundness of the
    transformation that Cpp2C performs *)

Require Import
  Coq.FSets.FMapList
  Coq.Logic.Classical_Prop
  Coq.Lists.List
  Coq.Strings.String
  Coq.ZArith.ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  MapLemmas
  EvalRules
  SideEffects
  NoCallsFromFunctionTable
  NoMacroInvocations
  NoVarsInEnvironment
  Transformations.


(*  If an expression has no side-effects, no nested macro invocations, and
    does not share any variables with its caller's environment, then
    it will evaluat to the same value whether it is invoked as the body of
    a macro, or called as the body of a function *)
(*  https://homepages.inf.ed.ac.uk/gdp/publications/cbn_cbv_lambda.pdf *)
Theorem no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil :
  forall mexpr,
  (* The macro body must not have side-effects *)
  ~ ExprHasSideEffects mexpr ->
  forall F M,
  (* The macro must not contain a macro invocation *)
  ExprNoMacroInvocations mexpr F M ->
  forall Ecaller,
  (* The macro body must not rely on variables from the caller's scope.
     Global variables, however, are allowed. *)
  ExprNoVarsInEnvironment mexpr Ecaller ->
  forall ef,
  MacroSubst nil nil mexpr ef ->
  forall S G v S''',
  EvalExpr S Ecaller G F M ef v S''' ->
  forall S' Ef Sargs l ls,
  EvalExprList S Ecaller G F M nil nil nil S' Ef Sargs l ls ->
  (* We will prove that S = S' since there are no side-effects.
     S' and Sargs must be distinct so that we don't overwrite pre-existing
     L-values *)
  NatMapProperties.Disjoint S' Sargs ->
  forall v0 S'''0,
  EvalExpr (NatMapProperties.update S' Sargs) Ef G F M mexpr v0 S'''0 ->
  v = v0.
Proof.
  intros.
  assert (NatMap.Equal (NatMapProperties.update S' Sargs) S'''0).
  { apply not_ExprHasSideEffects_S_Equal in H6; auto. }
  inversion H2; subst. clear H2.
  inversion H4; subst. clear H4.
  generalize dependent v0. 
  induction H3; intros; try (simpl in H; contradiction).
  - (* Macro expression is Num *)
    inversion H6; auto.
  - (* Macro expression is Local Var (contradiction) *)
    apply StringMap_mapsto_in in H4. inversion_clear H1.
    contradiction.
  - (* Macro expression is Global Var *)
    inversion_clear H9.
    + (* Call by value is Local Var (contradiction) *)
      apply StringMapFacts.empty_mapsto_iff in H11. contradiction.
    + (* Call by value is Global Var *)
      assert (l = l0). { apply StringMapFacts.MapsTo_fun with G x; auto. }
      subst l0. apply NatMapProperties.update_mapsto_iff in H13. destruct H13.
      * apply NatMapFacts.empty_mapsto_iff in H9. contradiction.
      * destruct H9. rewrite <- H2 in H9.
        apply NatMapFacts.MapsTo_fun with S l; auto. 
  - (* Macro is ParenExpr *)
    simpl in H. inversion_clear H0. inversion_clear H1.
    inversion_clear H6. auto.
  - (* Macro is UnExpr *)
    simpl in H. inversion_clear H0. inversion_clear H1.
    inversion_clear H6. assert (v = v1). apply IHEvalExpr; auto.
    subst v1; auto.
  - (* Macro is BinExpr *)
    simpl in H. apply Classical_Prop.not_or_and in H. destruct H.
    inversion_clear H0. inversion_clear H1. inversion_clear H6.
    assert (NatMap.Equal (NatMapProperties.update S (NatMap.empty Z)) S'0).
    { apply not_ExprHasSideEffects_S_Equal in H3_; auto. }
    rewrite <- H2 in *.
    assert (NatMap.Equal S'0 S'''0).
    { rewrite <- H6. rewrite <- H7. reflexivity. }
    assert (NatMap.Equal S'1 S'''0). { apply not_ExprHasSideEffects_S_Equal in H10; auto. }
    assert (v1 = v3).
    { apply IHEvalExpr1; auto.
      reflexivity.
      apply S'_Equal_EvalExpr with (S'_1:=S'1); auto. }
    assert (v2 = v4).
    { apply IHEvalExpr2; auto.
      apply not_ExprHasSideEffects_S_Equal in H3_; auto.
      symmetry. assumption.
      apply S_Equal_EvalExpr with (S_1:=S'1); auto.
      rewrite H2 in H6. rewrite <- H6 in H11. rewrite <- H11 in H12. assumption.
      }
    subst v3 v4; auto.
Qed.

(*  If an expression mexpr has no side-effects, no nested macro invocations,
    and does not share any variables with its caller's environment, and we
    substitute into it an expression e that also does not have side-effects
    or nested macro invocations, then the macro invocation with mexpr
    as its body and e as its argument will terminate to
    the same value as it would if mexpr were instead the body of a function
    and e were passed to that function as an argument *)
Lemma no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_1 :
  forall mexpr,
  (* The macro body must not have side-effects *)
  ~ ExprHasSideEffects mexpr ->
  forall F M,
  (* The macro must not contain a macro invocation *)
  ExprNoMacroInvocations mexpr F M ->
  forall Ecaller,
  (* The macro body must not rely on variables from the caller's scope.
     Global variables, however, are allowed. *)
  ExprNoVarsInEnvironment mexpr Ecaller ->
  forall e,
  (* The argument must not have side-effects *)
  ~ ExprHasSideEffects e ->
  (* The argument must not contain a macro invocation *)
  ExprNoMacroInvocations e F M->
  forall ef p,
  MacroSubst (p::nil) (e::nil) mexpr ef ->
  forall S G v S''',
  EvalExpr S Ecaller G F M ef v S''' ->
  forall v0_ S' Ef Sargs l ls,
  EvalExprList S Ecaller G F M (p::nil) (e::nil) (v0_::nil) S' Ef Sargs l ls ->
  (* We will prove that S = S' since there are no side-effects.
     S' and Sargs must be distinct so that we don't overwrite pre-existing
     L-values *)
  NatMapProperties.Disjoint S' Sargs ->
  forall v0 S'''0,
  EvalExpr (NatMapProperties.update S' Sargs) Ef G F M mexpr v0 S'''0 ->
  v = v0.
Proof.
  intros.
  assert (NatMap.Equal (NatMapProperties.update S' Sargs) S'''0).
  { apply not_ExprHasSideEffects_S_Equal in H8; auto. }
  inversion H4; subst. clear H4.
  inversion H6; subst. clear H6.
  inversion H17. subst. clear H17.
  inversion H23. subst. clear H23.
  generalize dependent v0_.
Abort.

(*  If an expression terminates to some value and final store before
    Cpp2C transforms it, and terminates to some value and final store
    after Cpp2C transforms it, then these two values and final stores
    are equal *)
Theorem transform_expr_sound_mut_v_s : forall M F e F' e',
  TransformExpr M F e F' e' ->
  (* The proof will not work if these variables were introduced sooner.
     Doing so would interfere with the induction hypothesis *)
  forall S E G v1 v2 S'1 S'2,
    EvalExpr S E G F M e v1 S'1 ->
    EvalExpr S E G F' M e' v2 S'2 ->
    v1 = v2 /\ NatMap.Equal S'1 S'2.
Proof.
  apply (TransformExpr_mut
    (* Induction rule for TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
    forall S E G v1 v2 S'1 S'2,
      EvalExpr S E G F M e v1 S'1 ->
      EvalExpr S E G F' M e' v2 S'2 ->
      v1 = v2 /\ NatMap.Equal S'1 S'2)
    (* Induction rule for TransformExprList *)
    (fun M F es F' es' (h : TransformExprList M F es F' es') =>
    forall S Ecaller G ps1 vs1 vs2 Snext1 Snext2 Ef1 Ef2 Sargs1 Sargs2 l1 l2 ls1 ls2,
      EvalExprList S Ecaller G F M ps1 es vs1 Snext1 Ef1 Sargs1 l1 ls1 ->
      EvalExprList S Ecaller G F' M ps1 es' vs2 Snext2 Ef2 Sargs2 l2 ls2 ->
      vs1 = vs2 /\ NatMap.Equal Snext1 Snext2 /\ StringMap.Equal Ef1 Ef2 /\ NatMap.Equal Sargs1 Sargs2 /\ l1 = l2 /\ ls1 = ls2)
    (* Induction rule for TransformStmt *)
    (fun M F stmt F' stmt' (h : TransformStmt M F stmt F' stmt') =>
    forall S E G S'1 S'2,
      EvalStmt S E G F M stmt S'1 ->
      EvalStmt S E G F' M stmt' S'2 ->
      NatMap.Equal S'1 S'2
      )); intros; auto.

  - (* Num *)
    inversion H. inversion H0. subst. split.
    auto. rewrite <- H7, <- H16. reflexivity.

  - (* Var *)
    inversion H; subst.
    + (* Untransformed is a local var *)
      inversion H0; subst.
      * (* Transformed is a local var *)
        apply StringMapFacts.find_mapsto_iff in H3, H5.
        rewrite H5 in H3. inversion H3; subst.
        apply NatMapFacts.find_mapsto_iff in H9, H12.
        rewrite H12 in H9. inversion H9. split.
        auto. rewrite <- H2, <- H4. reflexivity.
      * (* Transformed is a global var *)
        apply StringMap_mapsto_in in H3. contradiction.
    + (* Untransformed is a gloval var *)
      inversion H0; subst.
      * (* Transformed is a local var *)
        apply StringMap_mapsto_in in H6. contradiction.
      * (* Transformed is a global var *)
        apply StringMapFacts.find_mapsto_iff in H4, H7.
        rewrite H7 in H4. inversion H4; subst.
        apply NatMapFacts.find_mapsto_iff in H10, H14.
        rewrite H14 in H10. inversion H10. split.
        auto. rewrite <- H2, <- H5. reflexivity.

  - (* ParenExpr *)
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v1 v2 S'1 S'2; auto.

  - (* UnExpr *)
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v v0 S'1 S'2; auto.
    subst. auto.

  - (* BinExpr *)
    inversion_clear H1. inversion_clear H2.

    (* Prove that transformation of left operand is sound *)
    rewrite e0 in H1.
    apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr in H1; auto.
    eapply H in H1; eauto.
    destruct H1.
    subst v4.

    (* Prove that transformation of the right operand is sound *)
    eapply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr in H4; eauto.
    rewrite <- e in H4.
    apply H0 with (v1:=v3) (S'1:=S'1) in H5; auto.
    destruct H5. subst v5. auto.
    apply S_Equal_EvalExpr with (S_1:=S'); auto.

  - (* Assign *)
    inversion H0; subst.
    + inversion H1; subst.
      * apply StringMapFacts.find_mapsto_iff in H4, H5.
        rewrite H5 in H4. inversion H4; subst.
        destruct H with S E G v1 v2 S' S'0; auto.
        subst. split. auto. rewrite H13, H16. reflexivity.
      * apply StringMap_mapsto_in in H4. contradiction.
    + inversion H1; subst.
      * apply StringMap_mapsto_in in H6. contradiction.
      * apply StringMapFacts.find_mapsto_iff in H5, H7.
        rewrite H7 in H5. inversion H5; subst.
        destruct H with S E G v1 v2 S' S'0; auto.
        subst. split. auto. rewrite H14, H18. reflexivity.

  - (* CallOrInvocation *)
    inversion_clear H2.
    + (* Transformed is a function call *)
      inversion_clear H3.
      * (* Transformed is a function call *)

        assert (StringMap.MapsTo x (params, fstmt', fexpr') F'''').
        { subst F''''. apply StringMapProperties.update_mapsto_iff; left.
          apply StringMapFacts.add_mapsto_iff; auto. }

        assert ((params1, fstmt1, fexpr1) = (params, fstmt', fexpr')).
        { apply StringMapFacts.MapsTo_fun with F'''' x; auto. }
        inversion H25; subst params1 fstmt1 fexpr1; clear H25.

        assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
        { apply StringMapFacts.MapsTo_fun with F x; auto. }
        inversion H25; subst params0 fstmt0 fexpr0; clear H25.

        (* Prove argument transformation is sound *)
        rewrite e10 in H17.
        apply EvalExprListNoCallsFromFunctionTable_update_EvalExprListNoCallsFromFunctionTable in H17;
          auto.
        rewrite e1 in H17.
        apply EvalExprListNoCallsFromFunctionTable_update_EvalExprListNoCallsFromFunctionTable in H17;
          auto.
        rewrite e0 in H17.
        apply EvalExprListNoCallsFromFunctionTable_update_EvalExprListNoCallsFromFunctionTable in H17;
          auto.
        apply H with (vs1:=vs) (Snext1:=S') (Ef1:=Ef) (Sargs1:=Sargs) (l1:=l) (ls1:=ls) in H17; auto.
        destruct H17. destruct H25. destruct H26. destruct H27. destruct H28.
        subst vs0 ls0.

        assert (NatMap.Equal S'' S''0).
        { rewrite H11. rewrite H21. 
          rewrite H25, H27. reflexivity. }
        rewrite <- H17 in *.

        (* Prove statement transformation is sound *)
        rewrite e10 in H22.
        apply EvalStmtNoCallsFromFunctionTable_update_EvalStmtNoCallsFromFunctionTable in H22;
          auto.
        rewrite e1 in H22.
        apply EvalStmtNoCallsFromFunctionTable_update_EvalStmtNoCallsFromFunctionTable in H22;
          auto.
        apply H0 with (S'1:=S''') in H22; auto.
        2 : {
          subst F'.
          apply EvalStmtNoCallsFromFunctionTable_update_EvalStmtNoCallsFromFunctionTable; auto.
          apply S_Equal_EvalStmt with (S_1:=S''); auto.
          apply E_Equal_EvalStmt with (E_1:=Ef); auto. }

        (* Prove expression transformation is sound *)
        rewrite e10 in H23.
        apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr in H23; auto.
        apply H1 with (v1:=v1) (S'1:=S'''') in H23; auto.
        2 : {
          subst F''. apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr; auto.
          subst F'. apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr; auto.
          apply S_Equal_EvalExpr with (S_1:=S'''); auto.
          apply E_Equal_EvalExpr with (E_1:=Ef); auto. }

        destruct H23. subst v2. rewrite H24. rewrite <- H29. auto.

      * (* Transformed is a macro invocation  *)
        apply StringMap_mapsto_in in H2. contradiction.
    + (* Transformed is a macro invocation (contradiction) *)
      apply StringMap_mapsto_in in H4. contradiction.

  - (* Macro that is not transformable *)
    inversion_clear H.
    + (* Untransformed is a function call (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
    + (* Untransformed is a macro invocation *)
      inversion_clear H0.
      * (* Transformed is a function call (contradiction) *)
        apply StringMap_mapsto_in in m. contradiction.
      * (* Transformed is a macro invocation *)
        assert ((params0, mexpr0) = (params1, mexpr1)).
        { eapply StringMapFacts.MapsTo_fun; eauto. }
        inversion H0; subst; clear H0.
        assert (ef = ef0).
        { apply MacroSubst_deterministic with params1 es mexpr1; auto. }
        subst ef0. apply EvalExpr_deterministic with (v1:=v1) (S'1:=S'1) in H9; auto.

  - (* Object like macro without side-effects, shared variables with the caller environment,
       or nested macro invocations *)
    inversion H0. inversion H1.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + subst. apply StringMap_mapsto_in in m. contradiction.
    + inversion H1.
      subst S0 E0 G0 F0 M0 x0 es v1 S'1.
      subst S1 E1 G1 F1 M1 x1 es0 v2 S'''''.
      * (* Transformed is a function call *)
        (* Proof of equivalence *)

        (* Prove that the macro body does not change after transformation *)
        assert (mexpr = mexpr').
        { apply TransformExpr_ExprNoMacroInvocations_e_eq with M F F'; auto. }
        subst mexpr'.

        (* No side-effects in function *)

        (* Prove that the definition that we know the function maps to
           is the same one that we added during the transformation *)
        assert ( (params1, fstmt, fexpr) = (nil, Skip, mexpr) ).
        { subst newdef. apply StringMapFacts.MapsTo_fun with F' fname; auto.
          rewrite e3. apply StringMapFacts.add_mapsto_iff. auto. }
        inversion H2. subst params1 fstmt fexpr. clear H2.

        (* Add to the context all the premises we get from evaluating an
           empty argument list *)
        inversion H21.
        subst Sprev E G0 F0 M0 vs S'0 Ef Sargs l.

        (* Prove that there are no side-effects caused by the skip statement *)
        apply Skip_S_Equal in H26.

        (* Prove that there are no side-effects cause by the return expression *)
        assert (NatMap.Equal S'' S'''').
        { apply not_ExprHasSideEffects_S_Equal in H32; auto.
          rewrite <- H32. rewrite <- H26. reflexivity. }

        (* Prove that after freeing the memory allocated for the function
           environment, the store reverts back to its original state *)
        assert (NatMap.Equal S (NatMapProperties.restrict S'' S)).
        { rewrite H25. rewrite <- H2.
          apply NatMap_restrict_refl. }


        (* No side-effects in macro *)

        (* Prove that the definition that we know the macro maps to
           is the same one we asserted in the transformation *)
        assert ( (params, mexpr) = (params0, mexpr0) ).
        { apply StringMapFacts.MapsTo_fun with M x; auto. }
        inversion H8. subst params0 mexpr0. clear H8.

        (* Prove that after macro substitution, the macro body still
           does not have side-effects *)
        assert (~ ExprHasSideEffects ef).
        { apply not_ExprHasSideEffects_MacroSubst_not_ExprHasSideEffects with mexpr params nil; auto. }

        (* Prove that the macro invocation does not have side-effects *)
        assert (NatMap.Equal S S').
        { apply not_ExprHasSideEffects_S_Equal in H15; auto; auto. }
        rewrite <- H9. rewrite H7. rewrite H3. rewrite H35.

        (* Use one of our premises to assert that the macro does not contain
           variables from the caller environment *)
        (* NOTE: We should probably add the environment to the transformation
           relation so that we don't have to use such a generous premise *)
        assert (ExprNoVarsInEnvironment mexpr Ecaller).
        { apply e0 with S G v S'; auto. }
        assert (mexpr=ef). { inversion_clear H12; auto. } subst ef.
        split.
        -- (* Prove that the expression will result in the same value
               under call-by-name and call-by-value *)
           apply no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil with
            mexpr F' M' Ecaller mexpr S G S S (StringMap.empty nat) (NatMap.empty Z) 1 ls S'';
              auto.
           ++(* Prove that the macro body does contain a macro invocation *)
              subst M'. apply ExprNoMacroInvocations_remove_ExprNoMacroInvocations.
              apply TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations with F mexpr; auto.
           ++ constructor.
           ++ (* Prove that macro expression evaluation works the same
                  under an updated function table *)
              inversion H12. subst params mexpr0.
              subst F'. apply EvalExpr_notin_F_add_EvalExpr; auto.
              apply S'_Equal_EvalExpr with (S'_1:=S'); auto.
              symmetry. auto.
           ++ subst ls. constructor. reflexivity.
           ++ rewrite H2. auto.
           ++ (* Prove that function expression evaluation works the same
                 under an updated macro table *)
              subst M'. apply EvalExprNoMacroInvocations_remove_EvalExpr; auto.
              ** apply S_Equal_EvalExpr with (S_1:=S''').
                 --- apply S'_Equal_EvalExpr with (S'_1:=S''''); auto.
                     symmetry. auto.
                 --- rewrite <- H26. rewrite H2. auto.
              ** apply TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations with F mexpr; auto.
        -- reflexivity.
      * (* Transformed is a macro invocation (contradiction) *)
        apply StringMap_mapsto_in in H18. contradiction.

  - (* ExprList nil *)
    inversion H. inversion H0. subst. split; auto.
    split. rewrite <- H1, H8. reflexivity.
    split. reflexivity. split. reflexivity.
    auto.

  - (* ExprList cons *)
    inversion H1. inversion H2.
    destruct H with
      S Ecaller G v v0 Snext Snext0; auto. subst. inversion H32. subst.
    destruct H0 with
      Snext0 Ecaller G ps vs vs0 Snext1 Snext2 Ef' Ef'0 Sargs' Sargs'0 l1 l2 ls ls0; auto.
    apply S_Equal_EvalExprList with (S_1:=Snext); auto.
    destruct H4. destruct H8. destruct H9. destruct H10. subst.
    split; auto. split. rewrite <- H4. reflexivity.
    split. rewrite H8. reflexivity. split. rewrite H9. reflexivity.
    auto.

  - (* Stmt *)
    inversion H. inversion H0. subst. rewrite <- H1, <- H7. reflexivity.
Qed.

(* Issues:
           1) Proving evaluation equivalence under call-by-name and call-by-value

           Solutions:
           1) For now just prove for macros that have one argument.
*)
