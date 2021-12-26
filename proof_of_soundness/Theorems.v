Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.
From Cpp2C Require Import EvalRules.
From Cpp2C Require Import Transformations.

(* A constant macro is the same as a constant function with the same return
   expression *)
Lemma constant_function_macro_eq_to_function :
  forall i St E F M mname fname mexpr n,
  i = S n ->
  invocation mname M = Some mexpr ->
  definition mname F = None ->
  invocation fname M = None ->
  definition fname F = Some (Skip, mexpr) ->
  expreval i St E F M (CallOrInvocation fname) = 
  expreval i St E F M (CallOrInvocation mname).
Proof.
  intros.
  unfold expreval. rewrite H, H0, H1, H2, H3.
  induction n.
  - reflexivity.
  - reflexivity.
Qed.


(* A call to a macro without side-effects is equivalent to a call
   to the transformed version of that macro as a function *)
Lemma simple_macro_eq_func_call :
  forall (S S': state) (E : environment)
         (F F': func_definitions) (M M': macro_definitions)
         (mexpr: expr) (x fname : string)
         (v : Z),
  definition x F = None ->
  invocation x M = Some mexpr ->
  definition x F' = Some (Skip, mexpr) ->
  invocation x M' = None ->
  exprevalR S E F M mexpr v S' ->
  exprevalR S E F' M' mexpr v S' ->
  exprevalR S E F M (CallOrInvocation x) v S' <-> exprevalR S E F' M' (CallOrInvocation x) v S'.
Proof.
  intros.
  split.
  - intros.
    + eapply E_FunctionCall.
      * apply H1.
      * apply E_Skip.
      * apply H4.
  - intros. eapply E_MacroInvocation.
    * apply H0.
    * apply H3.
Qed.


(* We currently need this theorem for the soundndess proof.
   It basically says that if an expression could be evaluated under the
   original function list, it can be evaluated correctly under the
   transformed function list as well. We know this will be true in
   the implementation since we will guarantee that all the function
   names will be unique, but we need this for the proof. *)
Lemma eval_same_under_unique_names :
  forall S E F M v S' x mexpr,
  exprevalR S E F M mexpr v S' ->
  exprevalR S E (((x ++ "__as_function")%string, (Skip, mexpr)) :: F) M mexpr v S'.
Admitted.

(* This lemma asserts that if two operands of a binary expression can
   be successfully transformed, then their transformed function
   definition lists can be unioned and the evaluation of the operands
   will still be sound. Similar to above, intuitively this makes sense
   because the function names we generate will all be unique, but we
   need this lemma to assist in the Coq proof. *)
Lemma eval_same_under_joined_Fs :
  forall S E F M S' bo e1 e2 v1 v2 S'',
  exprevalR S E (transform_macros_F F M e1) M (transform_macros_e F M e1) v1 S' ->
  exprevalR S' E (transform_macros_F F M e2) M (transform_macros_e F M e2) v2 S'' ->
  exprevalR S E (transform_macros_F F M (BinExpr bo e1 e2)) M
  (transform_macros_e F M e1) v1 S'
  /\
  exprevalR S' E (transform_macros_F F M (BinExpr bo e1 e2)) M
  (transform_macros_e F M e2) v2 S''.
Proof.
Admitted.


Theorem transform_macros_sound :
  forall S E F M e v S',
  exprevalR S E F M e v S' ->
  exprevalR S E (transform_macros_F F M e) (transform_macros_M F M e) (transform_macros_e F M e) v S'.
Proof.
  intros.
  induction H; unfold transform_macros_M in *.
  - (* Num z *)
    apply E_Num.
  - (* X x *)
    apply E_X_Success with l.
    + apply H.
    + apply H0.
  - (* ParenExpr e *)
    apply E_ParenExpr. apply IHexprevalR.
  - (* UnExpr uo e *)
    apply E_UnExpr. apply IHexprevalR.
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
    apply E_Assign_Success. apply IHexprevalR. apply H0.
  - (* CallOrInvocation x (function call) *)
    unfold transform_macros_F. unfold transform_macros_e.
    rewrite H. apply E_FunctionCall with (fstmt:=fstmt) (fexpr:=fexpr)
    (S':=S'). apply H. apply H0. apply H1.
  - (* CallOrInvocation x (macro invocation) *)
    unfold transform_macros_F.
    unfold transform_macros_e.
    rewrite H.
    destruct (definition x F).
    + (* x is defined as a function
      (shouldn't happen so just use E_MacroInvocation *)
      apply E_MacroInvocation with mexpr. apply H. apply H0.
    + (* x is not defined as a function *)
      destruct (has_side_effects mexpr).
      * (* x's body has side-effects *)
        destruct (get_dynamic_vars mexpr).
           (* x does not have side-effects (does nothing) *)
        -- apply E_MacroInvocation with mexpr. apply H. apply H0.
           (* x  has side-effects (does nothing) *)
        -- apply E_MacroInvocation with mexpr. apply H. apply H0.
      * destruct (get_dynamic_vars mexpr).
           (* x does not share variables with the caller environment.
              Here is where we perform the simplest transformation. *)
        -- apply E_FunctionCall with (fstmt:=Skip) (fexpr:=mexpr) (S':=S).
           ++ unfold definition. unfold find.
              simpl. rewrite eqb_refl. auto.
           ++ apply E_Skip.
              (* Here is where we need a lemma stating that
                 under the new function list, the evaluation of the
                 transformed macro body will be the same.
                 Intuitively we know this will be true since all
                 the names in the transformed function list will be
                 unique, and we will only add names, never remove any. *)
           ++ apply eval_same_under_unique_names. apply H0.
           (* x shares variables with the caller environment *)
        -- apply E_MacroInvocation with mexpr. apply H. apply H0.
Qed.


(* Expression evaluation does not change under the ID transformation *)
Theorem transform_id_sound :
  forall S E F M e v S',
  exprevalR S E F M e v S' ->
  exprevalR S E F M (transform_id e) v S'.
Proof.
  intros.
  induction H.
  - (* Num z *)
    apply E_Num.
  - (* X x *)
    apply E_X_Success with l. apply H. apply H0.
  - (* ParenExpr e *)
    constructor. apply IHexprevalR.
  - (* UnExpr uo e *)
    constructor. apply IHexprevalR.
  - (* BinExpr bo e1 e2 *)
    apply E_BinExpr with (S:=S) (S':=S').
    apply IHexprevalR1. apply IHexprevalR2.
  - (* Assign x e *)
    constructor. apply IHexprevalR. apply H0.
  - (* CallOrInvocation x (function call) *)
    apply E_FunctionCall with (fstmt:=fstmt) (fexpr:=fexpr) (S':=S').
    apply H. apply H0. apply H1.
  - (* CallOrInvocation x (macro invocation) *)
   apply E_MacroInvocation with mexpr. apply H. apply H0.
Qed.


(* NOTE: May want to note in paper that we have to transform
         function and macro arguments recursively *)

(* We may need three separate theorems, proving
   1) Equivalence under expression transformation
   2) Equivalence function definitions transformation
   3) Equivalence under macro definitions transformation
   For proving 2 & 3, we can add to the premises of the proof
   that the other two transformations are sound
*)

