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
    (* Induction rule for TransformExprList *)
    (fun M F es F' es' (h : TransformExprList M F es F' es') =>
    forall S Ecaller G ps1 vs1 vs2 Snext1 Snext2 Ef1 Ef2 Sargs1 Sargs2 l1 l2 ls1 ls2,
      EvalExprList S Ecaller G F M ps1 es vs1 Snext1 Ef1 Sargs1 l1 ls1 ->
      EvalExprList S Ecaller G F' M ps1 es' vs2 Snext2 Ef2 Sargs2 l2 ls2 ->
      vs1 = vs2 /\ Snext1 = Snext2 /\ Ef1 = Ef2 /\ Sargs1 = Sargs2 /\ l1 = l2 /\ ls1 = ls2)
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

    (* Prove that transformation of left operand is sound *)
    rewrite e0 in H1.
    apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr in H1; auto.
    eapply H in H1; eauto.
    destruct H1.
    subst v4 S'0.

    (* Prove that transformation of the right operand is sound *)
    eapply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr in H4; eauto.
    rewrite <- e in H4.
    apply H0 with (v1:=v3) (S'1:=S'1) in H5; auto.
    destruct H5. subst v5 S'2. auto.
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
        subst Ef0 Sargs0 vs0 S'0 ls0.

        assert (S'' = S''0). {rewrite <- H11 in H21; auto. }
        rewrite <- H17 in *; clear H17.

        (* Prove statement transformation is sound *)
        rewrite e10 in H22.
        apply EvalStmtNoCallsFromFunctionTable_update_EvalStmtNoCallsFromFunctionTable in H22;
          auto.
        rewrite e1 in H22.
        apply EvalStmtNoCallsFromFunctionTable_update_EvalStmtNoCallsFromFunctionTable in H22;
          auto.
        apply H0 with (S'1:=S''') in H22; auto.
        2 : {
          subst F'. apply EvalStmtNoCallsFromFunctionTable_update_EvalStmtNoCallsFromFunctionTable; auto.
          }

        subst S'''0.

        (* Prove expression transformation is sound *)
        rewrite e10 in H23.
        apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr in H23; auto.
        apply H1 with (v1:=v1) (S'1:=S'''') in H23; auto.
        2 : {
          subst F''. apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr; auto.
          subst F'. apply EvalExpr_ExprNoCallsFromFunctionTable_update_EvalExpr; auto.
        }

        destruct H23. subst v2 S''''0. rewrite <- H14 in H24.
        apply NatMap_Equal_eq_iff in H14, H24. subst. auto.
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
        assert (mexpr=ef). { inversion_clear H12; auto. } subst ef.
        split.
        -- (* Prove that the expression will result in the same value
               under call-by-name and call-by-value *)
           apply no_side_effects_no_shared_vars_with_caller_evalargs_macrosubst_nil with
            mexpr F' M' Ecaller mexpr S G S S (StringMap.empty nat) (NatMap.empty Z) 1 ls S'';
              auto.
           ++ (* Prove that the macro body does contain a macro invocation *)
               subst M'. apply ExprNoMacroInvocations_remove_ExprNoMacroInvocations.
               apply TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations with F mexpr; auto.
           ++ constructor.
           ++ (* Prove that macro expression evaluation works the same
                  under an updated function table *)
              inversion H12. subst params mexpr0. clear H11.
              subst F'. apply EvalExpr_notin_F_add_EvalExpr; auto.
           ++ subst ls. constructor.
           ++ (* Prove that function expression evaluation works the same
                 under an updated macro table *)
              subst S'' M'. apply EvalExprNoMacroInvocations_remove_EvalExpr; auto.
              apply TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations with F mexpr; auto.
        -- auto.
      * apply StringMap_mapsto_in in H18. contradiction.

  - (* ExprList nil *)
    inversion H. inversion H0. subst. split; auto.

  - (* ExprList cons *)
    inversion H1. inversion H2.
    destruct H with S Ecaller G v v0 Snext Snext0; auto. subst. inversion H32. subst.
    destruct H0 with Snext0 Ecaller G ps vs vs0 Snext1 Snext2 Ef' Ef'0 Sargs' Sargs'0 l1 l2 ls ls0; auto.
    destruct H4. destruct H8. destruct H9. destruct H10. subst.
    split; auto.

  - (* Stmt *)
    inversion H. inversion H0. subst. auto.
Qed.


(* Issues:
           1) Proving evaluation equivalence under call-by-name and call-by-value
           2) Coq doesn't treat FMap.Equal as the same thing as Logic.eq

           Solutions:
           1) ???
           2) Just use an axiom stating that Equal implies eq. *) 
