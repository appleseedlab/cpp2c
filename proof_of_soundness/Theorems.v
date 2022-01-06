Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.
From Cpp2C Require Import EvalRules.
From Cpp2C Require Import Transformations.


(* We currently need this theorem for the soundndess proof.
   It basically says that if an expression could be evaluated under the
   original function list, it can be evaluated correctly under the
   transformed function list as well. We know this will be true in
   the implementation since we will guarantee that all the function
   names will be unique, but we need this for the proof. *)
Lemma expr_eval_same_under_unique_names :
  forall S E G F M v S' x params mexpr,
  invocation M x = Some (params, mexpr) ->
  exprevalR S E G F M mexpr v S' ->
  exprevalR S E G (((x ++ "__as_function")%string, (params, Skip, mexpr)) :: F) M mexpr v S'.
Admitted.


(* This lemma asserts that if two operands of a binary expression can
   be successfully transformed, then their transformed function
   definition lists can be unioned and the evaluation of the operands
   will still be sound. Similar to above, intuitively this makes sense
   because the function names we generate will all be unique, but we
   need this lemma to assist in the Coq proof. *)
Lemma eval_same_under_joined_Fs :
  forall S E G F M S' bo e1 e2 v1 v2 S'',
  exprevalR S E G (transform_macros_F_e F M e1) M (transform_macros_e F M e1) v1 S' ->
  exprevalR S' E G (transform_macros_F_e F M e2) M (transform_macros_e F M e2) v2 S'' ->
  exprevalR S E G (transform_macros_F_e F M (BinExpr bo e1 e2)) M
  (transform_macros_e F M e1) v1 S'
  /\
  exprevalR S' E G (transform_macros_F_e F M (BinExpr bo e1 e2)) M
  (transform_macros_e F M e2) v2 S''.
Admitted.

(* Transforming an expression involving macros to one in which
   transformable macros have been converted to functions results
   in an expression that evaluates to the same value and state; i.e.,
   the transformation is sound. *)
Theorem transform_macros_expressions_sound :
  forall S E G F M e v S',
  exprevalR S E G F M e v S' ->
  exprevalR S E G (transform_macros_F_e F M e) (transform_macros_M_e F M e) (transform_macros_e F M e) v S'.
Proof.
  intros.
  induction H; unfold transform_macros_M_e in *.
  - (* Num z *)
    apply E_Num.
  - (* X x (local var) *)
    apply E_X_Local with l.
    + apply H.
    + apply H0.
  - (* X x (global var) *)
    apply E_X_Global with l.
    + apply H.
    + apply H0.
    + apply H1.
  - (* ParenExpr e *)
    apply E_ParenExpr. fold transform_macros_e. apply IHexprevalR.
  - (* UnExpr uo e *)
    apply E_UnExpr. fold transform_macros_e. apply IHexprevalR.
  - (* BinExpr bo e1 e2 *)
    apply E_BinExpr with (S:=S) (S':=S'); fold transform_macros_e.
      (* We use an admitted lemma here to assert that if the operands
         of a binary expression can be transformed soundly, then
         the entire binary expression can be transformed soundly.
         This is to get around some issues with the uniqueness of
         function names. *)
    + apply eval_same_under_joined_Fs with (v2:=v2) (S'':=S'').
      apply IHexprevalR1. apply IHexprevalR2.
    + eapply eval_same_under_joined_Fs.
      apply IHexprevalR1. apply IHexprevalR2.
  - (* Assign x e *)
    apply E_Assign_Success. fold transform_macros_e.
    apply IHexprevalR. apply H0.
  - (* CallOrInvocation x (function call) *)
    unfold transform_macros_F_e. unfold transform_macros_e.
    rewrite H. apply E_FunctionCall with
      (params:=params) (fstmt:=fstmt) (fexpr:=fexpr) (S':=S').
      * apply H.
      * apply H0.
      * apply H1.
  - (* CallOrInvocation x (macro invocation) *)
    unfold transform_macros_F_e.
    unfold transform_macros_e.
    rewrite H.
    simpl.
    destruct (definition F x).
    + (* x is defined as a function (this will happen if there are
         name space clashes) *)
      apply E_MacroInvocation with params mexpr.
      * apply H.
      * apply H0.
    + (* x is not defined as a function *)
      destruct (has_side_effects mexpr).
      * (* x's body has side-effects *)
        destruct (get_dynamic_vars (params, mexpr)).
           (* x does not have side-effects (does nothing) *)
        -- apply E_MacroInvocation with params mexpr.
           ++ apply H.
           ++ apply H0.
           (* x  has side-effects (does nothing) *)
        -- apply E_MacroInvocation with params mexpr.
           ++ apply H.
           ++ apply H0.
      * destruct (get_dynamic_vars (params, mexpr)).
           (* x does not share variables with the caller environment.
              Here is where we perform the simplest transformation. *)
        -- apply E_FunctionCall with
          (params:=params) (fstmt:=Skip) (fexpr:=mexpr) (S':=S).
           ++ unfold definition. unfold find.
              simpl. rewrite eqb_refl. simpl. reflexivity.
           ++ apply E_Skip.
              (* Here is where we need a lemma stating that
                 under the new function list, the evaluation of the
                 transformed macro body will be the same.
                 Intuitively we know this will be true since all
                 the names in the transformed function list will be
                 unique, and we will only add names, never remove any. *)
           ++ apply expr_eval_same_under_unique_names.
              ** apply H.
              ** apply H0.
           (* x shares variables with the caller environment *)
        -- apply E_MacroInvocation with params mexpr.
           ++ apply H.
           ++ apply H0.
Qed.



(* This lemma says that if a transformed compound statement can be
   soundly evaluated, then each of its statements can be soundly
   evaluated as well. *)
(* This may need some work to be made more conservative *)
Lemma compound_statement_transformation_sound :
  forall S E G F M s0 rst stmts S' S'',
  stmtevalR S E G (transform_macros_F_s F M s0)
    (transform_macros_M_s F M s0)
    (transform_macros_s F M s0) S' ->
  stmtevalR S' E G
    (transform_macros_F_s F M (CompoundStmt rst))
    (transform_macros_M_s F M (CompoundStmt rst))
    (transform_macros_s F M (CompoundStmt rst)) S'' ->
  stmtevalR S E G (transform_macros_F_s F M (CompoundStmt stmts))
  (transform_macros_M_s F M (CompoundStmt stmts))
  (transform_macros_s F M s0) S'
  /\
  stmtevalR S' E G (transform_macros_F_s F M (CompoundStmt stmts))
  (transform_macros_M_s F M (CompoundStmt stmts))
  (CompoundStmt (map (transform_macros_s F M) rst)) S''.
Admitted.


(* Transforming a statement involving macros to one in which
   transformable macros have been converted to functions results
   in a statement that evaluates to the same state; i.e.,
   the transformation is sound. *)
Theorem transform_macros_statements_sound :
  forall S E G F M s S',
  stmtevalR S E G F M s S' ->
  stmtevalR S E G (transform_macros_F_s F M s) (transform_macros_M_s F M s) (transform_macros_s F M s) S'.
Proof.
  intros.
  induction H.
  - (* Skip *)
    apply E_Skip.
  - (* ExprStmt e *)
    apply E_ExprStmt with v.
    apply transform_macros_expressions_sound. apply H.
  - (* CompoundStmt nil *)
    apply E_CompoundStatementEmpty.
    (* The wrong s0 and rst are used here *)
  - (* CompoundStmt es *)
    apply E_CompoundStatementNotEmpty with
      (s0 := transform_macros_s F M s0)
        (rst := map (transform_macros_s F M) rst) (S' := S').
    + fold transform_macros_s. induction stmts.
      * discriminate.
      * simpl. inversion H. reflexivity.
    + fold transform_macros_s. induction stmts.
      * discriminate.
      * simpl in H0. rewrite H0. reflexivity.
    + apply compound_statement_transformation_sound with rst S''.
      * apply IHstmtevalR1.
      * apply IHstmtevalR2.
    + eapply compound_statement_transformation_sound.
      * apply IHstmtevalR1.
      * apply IHstmtevalR2.
  - (* IfStmt e s0 (false) *)
    apply E_IfFalse. admit.
  - (* IfStmt e s) (true) *)
    apply E_IfTrue with v S'.
    + apply H.
    + admit.
    + fold transform_macros_s. admit.
  - (* IfElseStmt e s0 s1 (false) *)
    apply E_IfElseFalse with S'.
    + admit.
    + fold transform_macros_s. admit.
  - (* IfElseStmt e s0 s1 (true) *)
    apply E_IfElseFalse with S'.
    + admit.
    + fold transform_macros_s. admit.
  - (* WhileStmt e s0 (false) *)
    apply E_WhileFalse. admit.
  - (* WhileStmt e s0 (true) *)
    apply E_WhileTrue with v S' S''.
    + apply H.
    + admit.
    + fold transform_macros_s. admit.
    + fold transform_macros_s. apply IHstmtevalR2.
Admitted.

(* NOTE: May want to note in paper that we have to transform
         function and macro arguments recursively *)
