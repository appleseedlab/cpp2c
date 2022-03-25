(*  Theorems.v
    Contains theorems directly concerning the soundness of the
    transformation that Cpp2C performs *)

(*  IDEA: Maybe we can prove call-by-name and call-by-value equivalence if
    the macro substitution relation evaluated its arguments while performing
    the substitution? *)

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
    ( fun M F e F' e' (h : TransformExpr M F e F' e') =>
      forall S E G v1 v2 S'1 S'2,
      EvalExpr S E G F M e v1 S'1 ->
      EvalExpr S E G F' M e' v2 S'2 ->
      v1 = v2 /\ NatMap.Equal S'1 S'2)
    (* Induction rule for TransformStmt *)
    ( fun M F s F' s' (h : TransformStmt M F s F' s') =>
      forall S E G S'1 S'2,
      EvalStmt S E G F M s S'1 ->
      EvalStmt S E G F' M s' S'2 ->
      NatMap.Equal S'1 S'2)
    (*  Induction rule for TransformExprList *)
    (fun M F es F' es' (h : TransformExprList M F es F' es') =>
      forall S E G S'1 S'2 esSimplified1 esSimplified2,
      EvalExprList S E G F M es S'1 esSimplified1 ->
      EvalExprList S E G F' M es' S'2 esSimplified2 ->
      NatMap.Equal S'1 S'2 /\ esSimplified1 = esSimplified2)
      ); intros; auto.

  - (* Num *)
    inversion H. inversion H0. subst. split.
    auto. rewrite <- H7, <- H16. reflexivity.

  - (* Var *)
    inversion H; subst.
    + (* Untransformed is a local var *)
      inversion H0; subst.
      * (* Transformed is a local var *)
        assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. } subst l0.
        assert (e=e0). { eapply NatMapFacts.MapsTo_fun; eauto. } subst e0.
        apply EvalExpr_deterministic with (v2:=v2) (S'2:=S'2) in H; auto.
      * (* Transformed is a global var *)
        apply StringMap_mapsto_in in H3. contradiction.
    + (* Untransformed is a gloval var *)
      inversion H0; subst.
      * (* Transformed is a local var *)
        apply StringMap_mapsto_in in H7. contradiction.
      * (* Transformed is a global var *)
        assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. } subst l0.
        assert (e=e0). { eapply NatMapFacts.MapsTo_fun; eauto. } subst e0.
        apply EvalExpr_deterministic with (v2:=v2) (S'2:=S'2) in H; auto.

  - (* ParenExpr *)
    inversion_clear H0. inversion_clear H1.
    destruct H with S E G v1 v2 S'1 S'2; auto.

  - (* UnExpr *)
    inversion H0. inversion H1. subst.
    destruct H with S E G v v0 S'1 S'2; auto.
    subst. auto.

  - (* BinExpr *)
    inversion_clear H1.
    inversion_clear H2.

    rewrite e0 in H1.
    apply e3 in H1.
    apply H with (v1:=v0) (S'1:=S') in H1; auto.
    destruct H1. subst v4.

    apply e4 in H4. rewrite <- e in H4.
    apply S_Equal_EvalExpr with (S2:=S'0) in H4; auto.
    eapply H0 in H4; eauto.
    destruct H4. subst v5. split. auto. auto.

  - (* Assign *)
    inversion_clear H0.
    + (*  Assign local *)
      inversion_clear H1.
      * (*  Assign local *)
        assert (l=l0). { eauto using StringMapFacts.MapsTo_fun. } subst l0.
        eapply H in H5; eauto. destruct H5. subst v2. split. auto.
        transitivity ((NatMapProperties.update S (NatMap.add l (Num v1) (NatMap.empty expr)))); auto;
          symmetry; auto.
      * (*  Assign global (contradiction) *)
        apply StringMap_mapsto_in in H2. contradiction.
    + (*  Assign global *)
      inversion_clear H1.
      * (*  Assign local (contradiction *)
        apply StringMap_mapsto_in in H0. contradiction.
      * (*  Assign global *)
        assert (l=l0). { eauto using StringMapFacts.MapsTo_fun. } subst l0.
        eapply H in H7; eauto. destruct H7. subst v2. split. auto.
        transitivity ((NatMapProperties.update S (NatMap.add l (Num v1) (NatMap.empty expr)))); auto;
          symmetry; auto.

  - (*  Function call *)
    inversion_clear H0.
    + (*  First is a function call *)
      * inversion_clear H1.
        --  (* Second is a function call *)
            assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
            { eauto using StringMapFacts.MapsTo_fun. }
            inversion H1; subst params0 fstmt0 fexpr0; clear H1.
            assert ((params1, fstmt1, fexpr1) = (params, fstmt, fexpr)).
            { apply StringMapFacts.MapsTo_fun with F' x; auto.
              rewrite e. apply StringMapProperties.update_mapsto_iff.
              right; auto. }
            inversion H1; subst params1 fstmt1 fexpr1; clear H1.
            clear H13.
            assert (ls = ls0).
            { assert (List.length es = List.length es').
              { eapply TransformExprList_length; eauto. }
              rewrite <- H1 in H14.
              transitivity (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)); auto. }
            rewrite <- H1 in *.
            clear H1 H4 H14. clear n m t H2 H3.
            assert (StringMap.Equal Ef Ef0).
            { transitivity (StringMapProperties.of_list (combine params ls)); auto;
              symmetry; auto. }
            clear H5 H15.
            eapply H in H16; eauto. destruct H16. subst es'1.
            assert (NatMap.Equal Sargs Sargs0).
            { transitivity (NatMapProperties.of_list (combine ls es'0)); auto;
              symmetry; auto. }
            assert (NatMap.Equal S'' S''0).
            { rewrite <- H2 in H19. rewrite <- H3 in H19.
              transitivity (NatMapProperties.update S' Sargs); auto;
                symmetry; auto. }
            clear H7 H17 H19 H6.

            rewrite e in H20. apply s in H20.
            eapply S_Equal_EvalStmt in H20; eauto; try symmetry; eauto.
            eapply E_Equal_EvalStmt in H20; eauto; try symmetry; eauto.
            apply EvalStmt_deterministic with (S'1:=S''') in H20; auto.

            rewrite e in H21. apply e0 in H21.
            eapply S_Equal_EvalExpr in H21; eauto; try symmetry; eauto.
            eapply E_Equal_EvalExpr in H21; eauto; try symmetry; eauto.
            apply EvalExpr_deterministic with (v1:=v1) (S'1:=S'''') in H21; auto.
            destruct H21. subst v2. split; auto.
            rewrite <- H6 in H22. transitivity (NatMapProperties.restrict S'''' S); auto;
              symmetry; auto.
        --  (* Second is a macro invocation (contradiction *)
            apply StringMap_mapsto_in in H0. contradiction.
    + (*  First is a macro invocation (contradiction) *)
      apply StringMap_mapsto_in in H2. contradiction.

  - (*  Transform macro identity *)
    inversion_clear H0.
    + (*  First is a function call (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
    + (*  First is a macro invocation *)
      * inversion_clear H.
        --  (* Second is a function call (contradiction) *)
            apply StringMap_mapsto_in in m. contradiction.
        --  (* Second is a macro invocation *)
            assert ((params0, mexpr0) = (params, mexpr)).
            { eauto using StringMapFacts.MapsTo_fun. }
            inversion H; subst params0 mexpr0; clear H.
            assert ((params1, mexpr1) = (params, mexpr)).
            { eapply StringMapFacts.MapsTo_fun; eauto. }
            inversion H; subst params1 mexpr1; clear H.
            clear H1 H0.
            assert (ls = ls0).
            { transitivity (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)); auto. }
            rewrite <- H in *.
            clear H2 H10 H.
            assert (StringMap.Equal Em Em0).
            { transitivity (StringMapProperties.of_list (combine params ls)); auto;
              symmetry; auto. }
            clear H3 H11.
            assert (NatMap.Equal Sargs Sargs0).
            { transitivity (NatMapProperties.of_list (combine ls es)); auto;
              symmetry; auto. }
            clear H4 H12.
            assert (NatMap.Equal S' S'0).
            { rewrite <- H0 in H14.
              transitivity (NatMapProperties.update S Sargs); auto; symmetry; auto. }
            clear H6 H14.
            assert (StringMap.Equal E' E'0).
            { rewrite <- H in H15.
              transitivity (StringMapProperties.update E Em); auto; symmetry; auto. }
            clear H7 H15.

            eapply S_Equal_EvalExpr in H16; try symmetry; eauto.
            eapply E_Equal_EvalExpr in H16; try symmetry; eauto.
            apply EvalExpr_deterministic with (v1:=v2) (S'1:=S'') in H16; auto.
            destruct H16. subst v2. split; auto.
            rewrite <- H4 in H17.
            transitivity (NatMapProperties.restrict S'' S); auto; symmetry; auto.

  - (*  Macro transformation *)
    assert (EvalExprList S E G F M es S'0 es'0).
    { apply e1 in H1; auto. }
    inversion_clear H1.
    + (*  First is a function call (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
    + (*  First is a macro invocation *)
      inversion_clear H2.
      * (* Second is a function call (actual transformation *)
        assert ((params, mexpr) = (params0, mexpr0)).
        { eapply StringMapFacts.MapsTo_fun; eauto. }
        inversion H2; subst params0 mexpr0; clear H2.
        assert ((params1, fstmt, fexpr) = (params, Skip, mexpr')).
        { eapply StringMapFacts.MapsTo_fun; eauto.
          rewrite e5. apply StringMapProperties.update_mapsto_iff. left.
          subst Fresult.
          apply StringMapFacts.add_mapsto_iff. left; auto. }
        inversion H2; subst params1 fstmt fexpr; clear H2.
        clear H4 H1 H13.

        assert (ls = ls0).
        { assert (List.length es = List.length es').
          { eapply TransformExprList_length; eauto. }
          rewrite <- H1 in *.
          transitivity (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)); auto;
            symmetry; auto. }
        rewrite <- H1 in *.
        clear H1 H5 H14.

        assert (StringMap.Equal Em Ef).
        { transitivity (StringMapProperties.of_list (combine params ls)); auto;
          symmetry; auto. }
        clear H15.

        assert (NatMap.Equal S S'3).
        { apply e9 in H16; auto. }
        rewrite <- H2 in H18.

        rewrite e5 in H16.
        apply e8 in H16.
        assert (NatMap.Equal S'0 S'3 /\ es'0 = es'1).
        { eapply H in H16; eauto. }
        destruct H4.
        subst es'1.

        assert (
          forall (v : Z) (S'0 : store),
            (EvalExpr S' E' G F M mexpr v S'0 <-> EvalExpr S''0 E' G F M mexpr v S'0) /\
            EvalExpr S''0 Em G F M mexpr v S'0
        ).
        { eapply a.
          - apply H3.
          - apply H7.
          - apply H17.
          - auto.
          - rewrite <- H2 in H19. auto.
          - apply H6.
          - apply H10. }
        assert (NatMap.Equal S''0 S''').
        { inversion_clear H20; auto. }
        clear H20.

        assert (NatMap.Equal S''' S'''').
        { apply e10 in H21; auto. }

        assert (NatMap.Equal S' S'').
        { apply e0 in H11; auto. }
        rewrite <- H15 in H12.
        rewrite H9 in H12.
        assert (NatMap.Equal S'1 S).
        { assert (NatMap.Equal S (NatMapProperties.restrict (NatMapProperties.update S Sargs) S)).
          { apply NatMap_disjoint_restrict_Equal; auto. }
          transitivity (NatMapProperties.restrict (NatMapProperties.update S Sargs) S); auto;
            symmetry; auto. }

        apply S_Equal_EvalExpr with (S2:=S''0) in H21; auto; try symmetry; auto.
        assert (EvalExpr S''0 Em G F M mexpr v1 S'').
        { apply H5. }
        eapply E_Equal_EvalExpr in H21; eauto; try symmetry; eauto.
        apply e6 in H23.
        rewrite <- e2 in H23.
        eapply H0 in H21; eauto. destruct H21.
        subst v2. split; auto.

        rewrite H22.
        rewrite H20. rewrite <- H14. rewrite <- H13. rewrite H19.
        rewrite <- H2.
        apply NatMap_disjoint_restrict_Equal. auto.
      * (*  Second is a macro invocation (contradiction) *)
        subst. apply StringMap_mapsto_in in H1. contradiction.

  - (*  Skip *)
    inversion_clear H. inversion_clear H0.
    transitivity S; auto; symmetry; auto.
  - (*  ExprStmt *)
    inversion_clear H0. inversion_clear H1.
    eapply H in H0; eauto. apply H0.
  - (*  IfElse *)
    inversion_clear H2.
    + (*  First is false *)
      inversion_clear H3.
      * (*  Second is false *)
        rewrite e1 in H2.
        apply e3 in H2.
        rewrite e0 in H2.
        apply e2 in H2.
        eapply H in H2; eauto. destruct H2. subst v0.

        eapply S_Equal_EvalStmt in H8; symmetry in H3; eauto.
        apply s3 in H6.
        rewrite <- e in H6.
        apply s4 in H6.
        rewrite <- e0 in H6.
        eapply H1 in H6; eauto.
      * (*  Second is true (contradiction) *)
        rewrite e1 in H2.
        apply e3 in H2.
        rewrite e0 in H2.
        apply e2 in H2.
        eapply H in H2; eauto. destruct H2. subst v0. contradiction.
    + (*  First is true *)
      inversion_clear H3.
      * (*  Second is false (contradiction) *)
        rewrite e1 in H2.
        apply e3 in H2.
        rewrite e0 in H2.
        apply e2 in H2.
        eapply H in H2; eauto. destruct H2. subst v0. contradiction.
      * (*  Second is true *)
        rewrite e1 in H2.
        apply e3 in H2.
        rewrite e0 in H2.
        apply e2 in H2.
        eapply H in H2; eauto. destruct H2. subst v0.

        eapply S_Equal_EvalStmt in H8; symmetry in H3; eauto.
        apply s in H6.
        rewrite <- e in H6.

        rewrite e1 in H8.
        apply s0 in H8.
        eapply H0 in H6; eauto.
  - (*  While *)
    inversion_clear H2.
    + (*  First is false *)
      inversion_clear H3.
      * (*  Second is false *)
        rewrite e0 in H2.
        apply e3 in H2.
        eapply H in H2; eauto.
        destruct H2. subst v0. auto.
      * (*  Second is true (contradiction) *)
        rewrite e0 in H2.
        apply e3 in H2.
        eapply H in H2; eauto. destruct H2. subst v0. contradiction.
    + (*  First is true *)
      inversion_clear H3.
      * (*  Second is false (contradiction) *)
        rewrite e0 in H2.
        apply e3 in H2.
        eapply H in H2; eauto. destruct H2. subst v0. contradiction.
      * (*  Second is true *)
        rewrite e0 in H2.
        apply e3 in H2.
        eapply H in H2; eauto.
        destruct H2. subst v0.

        eapply S_Equal_EvalStmt in H9; eauto; symmetry; eauto.
        apply s in H6.
        rewrite <- e in H6.
        eapply H0 in H6; eauto.


        eapply S_Equal_EvalStmt in H7; eauto; symmetry; eauto.
        apply s2 in H7.
        rewrite <- e in H7.
        apply s3 in H7.
        rewrite <- e0 in H7.
        eapply H1 in H7; eauto; try symmetry; eauto.

  - (*  CompoundStmt (nil) *)
    inversion_clear H. inversion_clear H0.
    transitivity S; auto; symmetry; auto.

  - (*  CompoundStmt (cons) *)
    inversion_clear H1. inversion_clear H2.
    rewrite e0 in H1.
    apply s0 in H1.
    eapply H in H1; eauto.
    eapply S_Equal_EvalStmt in H5; eauto; symmetry; eauto.
    apply s1 in H4.
    rewrite <- e in H4.
    eapply H0 in H5; eauto; try symmetry; eauto.

  - (*  ExprList (nil) *)
    inversion_clear H. inversion_clear H0.
    split; auto. transitivity S; auto; symmetry; auto.

  - (*  ExprList (cons) *)
    inversion_clear H1. inversion_clear H2.
    rewrite e1 in H1. apply e2 in H1.
    eapply H in H1; eauto. destruct H1.
    subst z0.

    eapply S_Equal_EvalExprList in H5; eauto; try symmetry; eauto.
    apply e3 in H4. rewrite <- e0 in H4.
    eapply H0 in H5; eauto.
    destruct H5. subst es'1. split; auto.
Qed.
