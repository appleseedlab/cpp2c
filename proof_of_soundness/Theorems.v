Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.
From Cpp2C Require Import EvalRules.
From Cpp2C Require Import Transformations.

Open Scope string_scope.

Section Theorems.

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


Theorem macro_transformation_sound :
  forall (S S': state) (E : environment)
         (F F': func_definitions) (M M': macro_definitions)
         (e e' mexpr: expr) (mname fname: string)
         (v : Z),
  definition mname F = None ->
  invocation mname M = Some mexpr ->
  has_side_effects mexpr = false ->
  get_dynamic_vars mexpr = nil ->
  exprevalR S E F M mexpr v S' ->
  exprevalR S E F' M' mexpr v S' ->
  e = CallOrInvocation mname ->
  (F', M', e') = transform_macros F M e ->
  exprevalR S E F M e v S' <-> exprevalR S E F' M' e' v S'.
Proof.
  intros. unfold transform_macros in H6.
  rewrite H5,H,H0,H1,H2 in H6. simpl in H6.
  inversion H6.
  split.
  - intros.
     + apply E_FunctionCall with (fstmt:=Skip) (fexpr:=mexpr) (S':=S).
      * unfold definition. simpl.
        rewrite eqb_refl. simpl. reflexivity.
      * apply E_Skip.
      * rewrite <- H8. rewrite <- H9. apply H4.
  - intros. rewrite H5. apply E_MacroInvocation with (mexpr := mexpr).
    + apply H0.
    + apply H3.
Qed.


Theorem macro_transformation_sound_all :
  forall (S S': state) (E : environment)
         (F F': func_definitions) (M M': macro_definitions)
         (e e' e'' mexpr: expr) (mname fname: string)
         (v : Z),
  definition mname F = None ->
  invocation mname M = Some mexpr ->
  has_side_effects mexpr = false ->
  get_dynamic_vars mexpr = nil ->
  (F', M', e') = transform_macros F M e ->
  exprevalR S E F M mexpr v S' ->
  exprevalR S E F' M' mexpr v S' ->
  exprevalR S E F M e v S' ->
  transform_macros F M (ParenExpr e'') = (F', M', e') ->
  exprevalR S E F' M' e' v S'.
Proof.
  intros. induction e.
  - inversion H3. apply H6.
  - inversion H3. apply H6.
  - Abort.



(* NOTE: May want to note in paper that we have to transform
         function and macro arguments recursively *)
(* TODO: Create a funtion that does an identity transform,
         then create a theorem that proves by induction
         that untransformed and transformed programs are
         identical *)

Theorem transform_id_eq :
  forall e,
  e = transform_id e.
Proof.
  intros.
  induction e.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite <- IHe. reflexivity.
  - simpl. rewrite <- IHe. reflexivity.
  - simpl. rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  - simpl. rewrite <- IHe. reflexivity.
  - reflexivity.
Qed.

Theorem id_args_eq : forall (args : list expr),
  args = map transform_id args.
Proof.
  intros.
  induction args.
  - reflexivity.
  - simpl. rewrite <- transform_id_eq. rewrite <- IHargs. reflexivity.
Qed.

(* We may need three separate theorems, proving
   1) Equivalence under expression transformation
   2) Equivalence function definitions transformation
   3) Equivalence under macro definitions transformation
   For proving 2 & 3, we can add to the premises of the proof
   that the other two transformations are sound
*)

End Theorems.

Close Scope string_scope.
