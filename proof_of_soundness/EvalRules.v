(*  EvalRules.v
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



Section Forall3.

  (*  Forall3: stating that elements of two lists are pairwise related. *)

  Variables A B C : Type.
  Variable R : A -> B -> C -> Prop.

  Inductive Forall3 : list A -> list B -> list C -> Prop :=
    | Forall3_nil : Forall3 nil nil nil
    | Forall3_cons : forall x y z xs ys zs,
      R x y z -> Forall3 xs ys zs -> Forall3 (x::xs) (y::ys) (z::zs).

  #[local]
  Hint Constructors Forall3 : core.
End Forall3.




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
    NatMap.Equal S S' ->
    EvalExpr S E G F M (Num z) z S'
  (*  Local variable lookup *)
  | E_LocalVar : forall S E G F M x l e v S',
    (*  Store does not change *)
    NatMap.Equal S S' ->
    (*  Variable is found in local environment *)
    StringMap.MapsTo x l E ->
    (*  L-value maps to an R-value *)
    NatMap.MapsTo l e S ->
    (*  Evaluate that R-value *)
    EvalExpr S E G F M e v S' ->
    EvalExpr S E G F M (Var x) v S'
  (*  Global variable lookup *)
  | E_GlobalVar : forall S E G F M x l e v S',
    (*  Store does not change *)
    NatMap.Equal S S' ->
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
  | E_Assign_Local : forall S E G F M l x e z S' S'',
    (*  Find the variable in the local environment *)
    StringMap.MapsTo x l E ->
    (*  Evaluate the RHS of the assignment *)
    EvalExpr S E G F M e z S' ->
    (*  Add the new mapping to the store *)
    NatMap.Equal S'' (NatMapProperties.update S (NatMap.add l (Num z) (NatMap.empty _))) ->
    EvalExpr S E G F M (Assign x e) z S''
  (*  Global variable assignment *)
  | E_Assign_Global : forall S E G F M l x e z S' S'',
    (*  The variable is not found in the local environment *)
    ~ StringMap.In x E ->
    (*  Find the variable in the global environment *)
    StringMap.MapsTo x l G ->
    (*  Evaluate the RHS of the assignment *)
    EvalExpr S E G F M e z S' ->
    (*  Add the new mapping to the store *)
    NatMap.Equal S'' (NatMapProperties.update S (NatMap.add l (Num z) (NatMap.empty _))) ->
    EvalExpr S E G F M (Assign x e) z S''
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
           Ef Sargs es' S' S'' S''' S'''' S''''' v,
    (*  TODO: Things to consider :
        - Should all functions have unique names?
        - Some of these premises could probably be removed
    *)
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
    NatMap.Equal Sargs (NatMapProperties.of_list (combine ls es')) ->

    (*  All the L-values used in the argument store do not appear
        in the original store. *)
    NatMapProperties.Disjoint S' Sargs ->
    (*  Combine the argument store into the original store *)
    NatMap.Equal S'' (NatMapProperties.update S' Sargs) ->
    (*  Evaluate the function's body under the caller's environment *)
    EvalStmt S'' Ef G F M fstmt S''' ->
    EvalExpr S''' Ef G F M fexpr v S'''' ->
    (*  Only keep in the store the L-value mappings that were there when
        the function was called; i.e., remove from the store all mappings
        whose L-value is in Ef/Sargs. *)
    NatMap.Equal S''''' (NatMapProperties.restrict S'''' S) ->
    EvalExpr S E G F M (CallOrInvocation x es) v S'''''
  (*  Macro invocation *)
  | E_MacroInvocation :
    forall S E G F M x es params mexpr ls
           Em E' Sargs S' S'' S''' v,
    (*  Mostly the same as function call, with a few key differences
        1) Macros are found in the macro table
        2) Macro definitions do not contain a statement
        3) Macro argument store is not evaluated
        4) Macro argument environment is unioned with the caller environment *)
    (*  Macro definitions shadow function definitions *)
    (*  Function name maps to some function *)
    StringMap.MapsTo x (params, mexpr) M ->

    (*  Deterministically create L-values *)
    ls = seq ((NatMap.cardinal S) + 1) (List.length es)%list ->
    (*  Deterministically create Ef and Sargs *)
    StringMap.Equal Em (StringMapProperties.of_list (combine params ls)) ->

    (*  Create the argument store *)
    NatMap.Equal Sargs (NatMapProperties.of_list (combine ls es)) ->

    (*  All the L-values used in the argument store do not appear
        in the original store. *)
    NatMapProperties.Disjoint S Sargs ->
    (*  Combine the argument store into the original store *)
    NatMap.Equal S' (NatMapProperties.update S Sargs) ->
    (*  Evaluate the macro's body under the caller's environment *)
    StringMap.Equal E' (StringMapProperties.update E Em) ->
    EvalExpr S' E' G F M mexpr v S'' ->
    (*  Only keep in the store the L-value mappings that were there when
        the macro was called; i.e., remove from the store all mappings
        whose L-value is in Ef/Sargs. *)
    NatMap.Equal S''' (NatMapProperties.restrict S'' S) ->
    EvalExpr S E G F M (CallOrInvocation x es) v S'''
with EvalStmt :
  store -> environment -> environment ->
  function_table -> macro_table ->
  stmt ->
  store -> Prop :=
  (*  A skip statement does not change the state *)
  | E_Skip : forall S E G F M S',
    NatMap.Equal S S' ->
    EvalStmt S E G F M Skip S'
  (*  An expr statement computes its expression *)
  | E_Expr : forall S E G F M e0 v S',
    EvalExpr S E G F M e0 v S' ->
    EvalStmt S E G F M (Expr e0) S'
  (*  An if-else whose condition evaluates to zero evaluates
      its second statement *)
  | E_IfElseFalse : forall S E G F M cond v S' s1 s2 S'',
    EvalExpr S E G F M cond v S' ->
    v = 0%Z ->
    EvalStmt S' E G F M s2 S'' ->
    EvalStmt S E G F M (IfElse cond s1 s2) S''
  (*  An if-else whose condition evaluates to non-zero evaluates
      its first statement *)
  | E_IfElseTrue: forall S E G F M cond v S' s1 s2 S'',
    EvalExpr S E G F M cond v S' ->
    v <> 0%Z ->
    EvalStmt S' E G F M s1 S'' ->
    EvalStmt S E G F M (IfElse cond s1 s2) S''
  (*  A while whose condition evaluates to false does
      not evaluate its body *)
  | E_WhileFalse: forall S E G F M cond v S' s0,
    EvalExpr S E G F M cond v S' ->
    v = 0%Z ->
    EvalStmt S E G F M (While cond s0) S'
  (*  A while whose condition evaluates to true evaluates
      its body, then is evaluated again *)
  | E_WhileTrue: forall S E G F M cond v S' s0 S'' S''',
    EvalExpr S E G F M cond v S' ->
    v <> 0%Z ->
    EvalStmt S' E G F M s0 S'' ->
    (*  NOTE: The fact that while loops are inductively defined
        by themselves can cause problems with proofs. When
        possible, try to induct over the evaluation relation,
        not any other relation your hypothesis includes *)
    EvalStmt S'' E G F M (While cond s0) S''' ->
    EvalStmt S E G F M (While cond s0) S'''
  (*  An empty compound statement does not change the state *)
  | E_CompoundStmt_nil: forall S E G F M S',
    NatMap.Equal S S' ->
    EvalStmt S E G F M (Compound nil) S'
  (*  A non-empty compound statement evaluates its head,
      then evaluates its remaining statements *)
  | E_CompoundStmt_cons: forall S E G F M s ss S' S'',
    EvalStmt S E G F M s S' ->
    EvalStmt S' E G F M (Compound ss) S'' ->
    EvalStmt S E G F M (Compound (s::ss)) S''
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
    NatMap.Equal S S' ->
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
Scheme EvalExpr_mut := Induction for EvalExpr Sort Prop
with EvalStmt_mut := Induction for EvalStmt Sort Prop
with EvalExprList_mut := Induction for EvalExprList Sort Prop.


(*  If an expression e terminates under some context with an initial store S,
    and some other store S2 is equal to S, then e will also terminate
    under the original context where S has been replaced with S2 *)
Lemma S_Equal_EvalExpr : forall S1 E G F M e v S',
  EvalExpr S1 E G F M e v S' ->
  forall S2,
  NatMap.Equal S1 S2 ->
  EvalExpr S2 E G F M e v S'.
Proof.
  apply (EvalExpr_mut
      (*  EvalExpr *)
      (fun S1 E G F M e v S' (h : EvalExpr S1 E G F M e v S' ) =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalExpr S2 E G F M e v S')
      (*  EvalStmt *)
      (fun S1 E G F M stmt S' (h : EvalStmt S1 E G F M stmt S' ) =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalStmt S2 E G F M stmt S')
      (*  EvalExprList *)
      (fun S1 E G F M es S' es'
        (h : EvalExprList S1 E G F M es S' es') =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalExprList S2 E G F M es S' es')
    ); intros.
  - (*  Num *)
    rewrite H in e. constructor; auto.
  - (*  Local var *)
    rewrite H0 in e0. apply E_LocalVar with l e; auto. rewrite <- H0; auto.
  - (*  Global var *)
     rewrite H0 in e0. apply E_GlobalVar with l e; auto. rewrite <- H0; auto.
  - (*  ParenExpr *)
     constructor. apply H; auto.
  - (*  UnExpr *)
     constructor. apply H; auto.
  - (*  BinExpr *)
      apply E_BinExpr with S'.
      * (*  Left operand *)
        apply H. auto.
      * (*  Right operand *)
        apply H0; reflexivity.
  - (*  Local assignment *)
    rewrite H0 in e1. apply E_Assign_Local with l S'; auto.
  - (*  Global assignment *)
    rewrite H0 in e1. apply E_Assign_Global with l S'; auto.
  - (*  Function call *)
    apply E_FunctionCall with params fstmt fexpr ls Ef Sargs es' S' S'' S''' S''''; auto.
    + assert (NatMap.cardinal S2 = NatMap.cardinal S).
      { apply NatMapProperties.Equal_cardinal. symmetry. auto. }
      rewrite H3. auto.
    + rewrite <- H2. auto.
  - (*  Macro invocation *)
    apply E_MacroInvocation with params mexpr ls Em E' Sargs S' S'' ; auto; try (rewrite <- H0; auto).
  - (*  Statements *)
    constructor. rewrite H in e; auto.
  - (*  Expr *)
    econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto. symmetry. rewrite <- e. auto.
  - econstructor 8; eauto.
  - (*  ExprList (nil) *)
    constructor. rewrite H in e; auto.
  - (*  ExprList (cons) *)
    apply E_ExprList_cons with S'; auto.
Qed.


Lemma S_Equal_EvalStmt : forall S1 E G F M s S',
  EvalStmt S1 E G F M s S' ->
  forall S2,
  NatMap.Equal S1 S2 ->
  EvalStmt S2 E G F M s S'.
Proof.
  apply (EvalStmt_mut
      (*  EvalExpr *)
      (fun S1 E G F M e v S' (h : EvalExpr S1 E G F M e v S' ) =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalExpr S2 E G F M e v S')
      (*  EvalStmt *)
      (fun S1 E G F M stmt S' (h : EvalStmt S1 E G F M stmt S' ) =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalStmt S2 E G F M stmt S')
      (*  EvalExprList *)
      (fun S1 E G F M es S' es'
        (h : EvalExprList S1 E G F M es S' es') =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalExprList S2 E G F M es S' es')
    ); intros.
  - (*  Num *)
    rewrite H in e. constructor; auto.
  - (*  Local var *)
    rewrite H0 in e0. apply E_LocalVar with l e; auto. rewrite <- H0; auto.
  - (*  Global var *)
     rewrite H0 in e0. apply E_GlobalVar with l e; auto. rewrite <- H0; auto.
  - (*  ParenExpr *)
     constructor. apply H; auto.
  - (*  UnExpr *)
     constructor. apply H; auto.
  - (*  BinExpr *)
      apply E_BinExpr with S'.
      * (*  Left operand *)
        apply H. auto.
      * (*  Right operand *)
        apply H0; reflexivity.
  - (*  Local assignment *)
    rewrite H0 in e1. apply E_Assign_Local with l S'; auto.
  - (*  Global assignment *)
    rewrite H0 in e1. apply E_Assign_Global with l S'; auto.
  - (*  Function call *)
    apply E_FunctionCall with params fstmt fexpr ls Ef Sargs es' S' S'' S''' S''''; auto.
    + assert (NatMap.cardinal S2 = NatMap.cardinal S).
      { apply NatMapProperties.Equal_cardinal. symmetry. auto. }
      rewrite H3. auto.
    + rewrite <- H2. auto.
  - (*  Macro invocation *)
    apply E_MacroInvocation with params mexpr ls Em E' Sargs S' S'' ; auto; try (rewrite <- H0; auto).
  - (*  Statements *)
    constructor. rewrite H in e; auto.
  - (*  Expr *)
    econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto. symmetry. rewrite <- e. auto.
  - econstructor 8; eauto.
  - (*  ExprList (nil) *)
    constructor. rewrite H in e; auto.
  - (*  ExprList (cons) *)
    apply E_ExprList_cons with S'; auto.
Qed.


Lemma S_Equal_EvalExprList : forall S1 E G F M es S' es',
  EvalExprList S1 E G F M es S' es' ->
  forall S2,
  NatMap.Equal S1 S2 ->
  EvalExprList S2 E G F M es S' es'.
Proof.
  apply (EvalExprList_mut
      (*  EvalExpr *)
      (fun S1 E G F M e v S' (h : EvalExpr S1 E G F M e v S' ) =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalExpr S2 E G F M e v S')
      (*  EvalStmt *)
      (fun S1 E G F M stmt S' (h : EvalStmt S1 E G F M stmt S' ) =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalStmt S2 E G F M stmt S')
      (*  EvalExprList *)
      (fun S1 E G F M es S' es'
        (h : EvalExprList S1 E G F M es S' es') =>
        forall S2,
        NatMap.Equal S1 S2 ->
        EvalExprList S2 E G F M es S' es')
    ); intros.
  - (*  Num *)
    rewrite H in e. constructor; auto.
  - (*  Local var *)
    rewrite H0 in e0. apply E_LocalVar with l e; auto. rewrite <- H0; auto.
  - (*  Global var *)
     rewrite H0 in e0. apply E_GlobalVar with l e; auto. rewrite <- H0; auto.
  - (*  ParenExpr *)
     constructor. apply H; auto.
  - (*  UnExpr *)
     constructor. apply H; auto.
  - (*  BinExpr *)
      apply E_BinExpr with S'.
      * (*  Left operand *)
        apply H. auto.
      * (*  Right operand *)
        apply H0; reflexivity.
  - (*  Local assignment *)
    rewrite H0 in e1. apply E_Assign_Local with l S'; auto.
  - (*  Global assignment *)
    rewrite H0 in e1. apply E_Assign_Global with l S'; auto.
  - (*  Function call *)
    apply E_FunctionCall with params fstmt fexpr ls Ef Sargs es' S' S'' S''' S''''; auto.
    + assert (NatMap.cardinal S2 = NatMap.cardinal S).
      { apply NatMapProperties.Equal_cardinal. symmetry. auto. }
      rewrite H3. auto.
    + rewrite <- H2. auto.
  - (*  Macro invocation *)
    apply E_MacroInvocation with params mexpr ls Em E' Sargs S' S'' ; auto; try (rewrite <- H0; auto).
  - (*  Statements *)
    constructor. rewrite H in e; auto.
  - (*  Expr *)
    econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto. symmetry. rewrite <- e. auto.
  - econstructor 8; eauto.
  - (*  ExprList (nil) *)
    constructor. rewrite H in e; auto.
  - (*  ExprList (cons) *)
    apply E_ExprList_cons with S'; auto.
Qed.


Lemma E_Equal_EvalStmt : forall S E1 G F M s S',
  EvalStmt S E1 G F M s S' ->
  forall E2,
  StringMap.Equal E1 E2 ->
  EvalStmt S E2 G F M s S'.
Proof.
  apply (EvalStmt_mut
      (*  EvalExpr *)
      (fun S E1 G F M e v S' (h : EvalExpr S E1 G F M e v S' ) =>
        forall E2,
        StringMap.Equal E1 E2 ->
        EvalExpr S E2 G F M e v S')
      (*  EvalStmt *)
      (fun S E1 G F M s S' (h : EvalStmt S E1 G F M s S' ) =>
        forall E2,
        StringMap.Equal E1 E2 ->
        EvalStmt S E2 G F M s S')
      (*  EvalExprList *)
      (fun S E1 G F M es S' es'
        (h : EvalExprList S E1 G F M es S' es') =>
        forall E2,
        StringMap.Equal E1 E2 ->
        EvalExprList S E2 G F M es S' es')
    ); intros.
  - (*  Num *)
    constructor; auto.
  - (*  Local var *)
    apply E_LocalVar with l e; auto. rewrite <- H0; auto.
  - (*  Global var *)
     apply E_GlobalVar with l e; auto. rewrite <- H0; auto.
  - (*  ParenExpr *)
     constructor. apply H; auto.
  - (*  UnExpr *)
     constructor. apply H; auto.
  - (*  BinExpr *)
      apply E_BinExpr with S'.
      * (*  Left operand *)
        apply H. auto.
      * (*  Right operand *)
        apply H0; auto.
  - (*  Local assignment *)
    rewrite H0 in m. apply E_Assign_Local with l S'; auto.
  - (*  Global assignment *)
    rewrite H0 in n. apply E_Assign_Global with l S'; auto.
  - (*  Function call *)
    apply E_FunctionCall with params fstmt fexpr ls Ef Sargs es' S' S'' S''' S''''; auto.
  - (*  Macro invocation *)
    apply E_MacroInvocation with params mexpr ls Em E' Sargs S' S''; auto.
    rewrite <- H0. assumption.
  - (*  Statements *)
    constructor; auto.
  - (*  Expr *)
    econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto.
  - econstructor 8; eauto.
  - (*  ExprList (nil) *)
    constructor; auto.
  - (*  ExprList (cons) *)
    apply E_ExprList_cons with S'; auto.
Qed.


Lemma E_Equal_EvalExpr : forall S E1 G F M e v S',
  EvalExpr S E1 G F M e v S' ->
  forall E2,
  StringMap.Equal E1 E2 ->
  EvalExpr S E2 G F M e v S'.
Proof.
  apply (EvalExpr_mut
      (*  EvalExpr *)
      (fun S E1 G F M e v S' (h : EvalExpr S E1 G F M e v S' ) =>
        forall E2,
        StringMap.Equal E1 E2 ->
        EvalExpr S E2 G F M e v S')
      (*  EvalStmt *)
      (fun S E1 G F M s S' (h : EvalStmt S E1 G F M s S' ) =>
        forall E2,
        StringMap.Equal E1 E2 ->
        EvalStmt S E2 G F M s S')
      (*  EvalExprList *)
      (fun S E1 G F M es S' es'
        (h : EvalExprList S E1 G F M es S' es') =>
        forall E2,
        StringMap.Equal E1 E2 ->
        EvalExprList S E2 G F M es S' es')
    ); intros.
  - (*  Num *)
    constructor; auto.
  - (*  Local var *)
    apply E_LocalVar with l e; auto. rewrite <- H0; auto.
  - (*  Global var *)
     apply E_GlobalVar with l e; auto. rewrite <- H0; auto.
  - (*  ParenExpr *)
     constructor. apply H; auto.
  - (*  UnExpr *)
     constructor. apply H; auto.
  - (*  BinExpr *)
      apply E_BinExpr with S'.
      * (*  Left operand *)
        apply H. auto.
      * (*  Right operand *)
        apply H0; auto.
  - (*  Local assignment *)
    rewrite H0 in m. apply E_Assign_Local with l S'; auto.
  - (*  Global assignment *)
    rewrite H0 in n. apply E_Assign_Global with l S'; auto.
  - (*  Function call *)
    apply E_FunctionCall with params fstmt fexpr ls Ef Sargs es' S' S'' S''' S''''; auto.
  - (*  Macro invocation *)
    apply E_MacroInvocation with params mexpr ls Em E' Sargs S' S'' ; auto; try (rewrite <- H0; auto).
  - (*  Statements *)
    constructor; auto.
  - (*  Expr *)
    econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto.
  - econstructor 8; eauto.
  - (*  ExprList (nil) *)
    constructor; auto.
  - (*  ExprList (cons) *)
    apply E_ExprList_cons with S'; auto.
Qed.


Lemma EvalExpr_deterministic : forall S E G F M e v1 S'1,
  EvalExpr S E G F M e v1 S'1 ->
  forall v2 S'2,
  EvalExpr S E G F M e v2 S'2 ->
  v1 = v2 /\ NatMap.Equal S'1 S'2.
Proof.
  apply (EvalExpr_mut
      (*  EvalExpr *)
      (fun S E G F M e v1 S'1 (h : EvalExpr S E G F M e v1 S'1 ) =>
        forall v2 S'2,
          EvalExpr S E G F M e v2 S'2 ->
          v1 = v2 /\ NatMap.Equal S'1 S'2)
      (*  EvalStmt *)
      (fun S E G F M stmt S'1 (h : EvalStmt S E G F M stmt S'1 ) =>
        forall S'2,
          EvalStmt S E G F M stmt S'2 ->
          NatMap.Equal S'1 S'2)
      (*  EvalExprList *)
      (fun S E G F M es S'1 es'1
        (h : EvalExprList S E G F M es S'1 es'1) =>
        forall S'2 es'2,
          EvalExprList S E G F M es S'2 es'2 ->
          NatMap.Equal S'1 S'2 /\ es'1 = es'2)
    ); intros; auto.
  - inversion_clear H. split; auto. transitivity S; auto. symmetry; auto.
  - (*  Local Var *)
    inversion_clear H0.
    + (*  Local *)
      assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst l0.
      assert (e=e2). { eapply NatMapFacts.MapsTo_fun; eauto. }
      subst e2. auto.
    + (*  Global (contradiction *)
      apply StringMap_mapsto_in in m. contradiction.
  - (*  Global Var *)
    inversion_clear H0.
    + (*  Local *)
      apply StringMap_mapsto_in in H2. contradiction.
    + (*  Global (contradiction *)
      assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst l0.
      assert (e=e2). { eapply NatMapFacts.MapsTo_fun; eauto. }
      subst e2. auto.
  - (*  ParenExpr *)
    inversion_clear H0; auto.
  - (*  UnExpr *)
      inversion_clear H0.
      destruct H with v0 S'2; auto. subst. auto.
  - (*  BinExpr *)
    inversion_clear H1.
    (*  Left operand*)
    assert (v1 = v3 /\ NatMap.Equal S' S'0). { auto. }
    destruct H1; subst.
    (*  Right operand *)
    assert (v2 = v4 /\ NatMap.Equal S'' S'2).
    { apply H0. apply S_Equal_EvalExpr with S'0; auto. symmetry. auto. }
    destruct H1; subst. auto.
  - (*  Local Assignment *)
    inversion_clear H0.
    + (*  Local assignment *)
      assert (z = v2 /\ NatMap.Equal S' S'0). { auto. }
      destruct H0. subst v2.
      assert (l0 = l). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst. rewrite <- H3 in e1. auto.
    + (*  Global assignment (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
  - (*  Global Assignment *)
    inversion_clear H0.
    + (*  Local assignment (contradiction) *)
      apply StringMap_mapsto_in in H1. contradiction.
    + (*  Global assignment *)
      assert (z = v2 /\ NatMap.Equal S' S'0). { auto. }
      destruct H0. subst v2.
      assert (l0 = l). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst. auto. rewrite <- H4 in e1. auto.
  -  (*  Function call *)
    inversion_clear H2.
    + (*  Function call *)
      assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
      { eapply StringMapFacts.MapsTo_fun; eauto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      assert (NatMap.Equal S' S'0 /\  es' = es'0). { auto. }
      destruct H2. subst es'0.

      assert (ls = ls0).
      { transitivity (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)); auto. }
      rewrite <- H14 in *; clear H14.
      assert (StringMap.Equal Ef Ef0).
      { transitivity (StringMapProperties.of_list (combine params ls)); auto; symmetry; auto. }
      assert (NatMap.Equal Sargs Sargs0).
      { transitivity (NatMapProperties.of_list (combine ls es')); auto; symmetry; auto. }
      assert (NatMap.Equal S'' S''0).
      { rewrite <- H2 in H10. rewrite <- H15 in H10.
      transitivity (NatMapProperties.update S' Sargs); auto; symmetry; auto. }

      apply S_Equal_EvalStmt with (S2:=S'') in H11; try symmetry; auto.
      apply E_Equal_EvalStmt with (E2:=Ef) in H11; try symmetry; auto.
      apply H0 in H11.
      apply S_Equal_EvalExpr with (S2:=S''') in H12; try symmetry; auto.
      apply E_Equal_EvalExpr with (E2:=Ef) in H12; try symmetry; auto.
      apply H1 in H12. destruct H12.
      rewrite <- H17 in H13. rewrite H13. rewrite e6. subst v2.
      split; reflexivity.
    + (*  Macro invocation (contradiction) *)
      apply StringMap_mapsto_in in H3. contradiction.
  - (*  Macro invocation *)
    inversion_clear H0.
    + (*  Function call (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
    + (*  Macro invocation *)

      assert ((params0, mexpr0) = (params, mexpr)).
      { eapply StringMapFacts.MapsTo_fun; eauto. }
      inversion H0; subst params0 mexpr0; clear H0.

      assert (ls = ls0).
      { transitivity (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)); auto. }
      rewrite <- H0 in *; clear H0.
      assert (StringMap.Equal Em Em0).
      { transitivity (StringMapProperties.of_list (combine params ls)); auto; symmetry; auto. }
      assert (NatMap.Equal Sargs Sargs0).
      { transitivity (NatMapProperties.of_list (combine ls es)); auto; symmetry; auto. }
      assert (NatMap.Equal S' S'0).
      { rewrite <- H10 in H6.
      transitivity (NatMapProperties.update S Sargs); auto; symmetry; auto. }
      assert (StringMap.Equal E' E'0).
      { rewrite H3 in H7. rewrite e0 in e3.
        transitivity (StringMapProperties.update E (StringMapProperties.of_list (combine params ls))); auto.
        symmetry; auto. }
      apply E_Equal_EvalExpr with (E2:=E') in H8; try symmetry; auto.
      apply S_Equal_EvalExpr with (S2:=S') in H8; try symmetry; auto.
      apply H in H8.
      destruct H8. subst v2. split; auto.
      rewrite <- H13 in H9.
      transitivity (NatMapProperties.restrict S'' S); auto; symmetry; auto.

  - inversion_clear H. transitivity S; auto; try symmetry; auto.
  - inversion_clear H0. apply H in H1. destruct H1; auto.
  - inversion_clear H1.
    + apply H in H2. destruct H2. apply S_Equal_EvalStmt with (S2:=S') in H4; symmetry; auto.
      apply H0 in H4. symmetry; auto.
    + apply H in H2. destruct H2. subst v0. contradiction.
  - inversion_clear H1.
    + apply H in H2. destruct H2. subst v0. contradiction.
    + apply H in H2. destruct H2. apply S_Equal_EvalStmt with (S2:=S') in H4; symmetry; auto.
      apply H0 in H4. symmetry; auto.
  - inversion_clear H0.
    + apply H with v0 S'2 in H1. destruct H1. auto.
    + apply H with v0 S'0 in H1. destruct H1. subst v0. contradiction.
  - inversion_clear H2.
    + apply H with v0 S'2 in H3; auto. destruct H3. subst v0. contradiction.
    + apply H with v0 S'0 in H3; auto. destruct H3. subst v0.
      apply S_Equal_EvalStmt with (S2:=S') in H5. 2 : { symmetry; auto. }
      apply H0 with S''0 in H5. apply H1. eapply S_Equal_EvalStmt; eauto.
      symmetry. auto.
  - inversion_clear H. transitivity S; auto. symmetry; auto.
  - inversion_clear H1. apply H in H2.
    apply S_Equal_EvalStmt with (S2:=S') in H3; auto; symmetry; auto.
  - inversion_clear H. split; auto. transitivity S; auto. rewrite e; reflexivity.
  - inversion_clear H1.
    apply H in H2. destruct H2. subst z0.
    apply S_Equal_EvalExprList with (S2:=S') in H3.
    apply H0 in H3. destruct H3. subst es'0. split; auto.
    symmetry. auto.
Qed.


Lemma EvalStmt_deterministic : forall S E G F M s S'1,
  EvalStmt S E G F M s S'1 ->
  forall S'2,
  EvalStmt S E G F M s S'2 ->
  NatMap.Equal S'1 S'2.
Proof.
  apply (EvalStmt_mut
      (*  EvalExpr *)
      (fun S E G F M e v1 S'1 (h : EvalExpr S E G F M e v1 S'1 ) =>
        forall v2 S'2,
          EvalExpr S E G F M e v2 S'2 ->
          v1 = v2 /\ NatMap.Equal S'1 S'2)
      (*  EvalStmt *)
      (fun S E G F M stmt S'1 (h : EvalStmt S E G F M stmt S'1 ) =>
        forall S'2,
          EvalStmt S E G F M stmt S'2 ->
          NatMap.Equal S'1 S'2)
      (*  EvalExprList *)
      (fun S E G F M es S'1 es'1
        (h : EvalExprList S E G F M es S'1 es'1) =>
        forall S'2 es'2,
          EvalExprList S E G F M es S'2 es'2 ->
          NatMap.Equal S'1 S'2 /\ es'1 = es'2)
    ); intros; auto.
  - inversion_clear H. split; auto. transitivity S; auto. symmetry; auto.
  - (*  Local Var *)
    inversion_clear H0.
    + (*  Local *)
      assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst l0.
      assert (e=e2). { eapply NatMapFacts.MapsTo_fun; eauto. }
      subst e2. auto.
    + (*  Global (contradiction *)
      apply StringMap_mapsto_in in m. contradiction.
  - (*  Global Var *)
    inversion_clear H0.
    + (*  Local *)
      apply StringMap_mapsto_in in H2. contradiction.
    + (*  Global (contradiction *)
      assert (l=l0). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst l0.
      assert (e=e2). { eapply NatMapFacts.MapsTo_fun; eauto. }
      subst e2. auto.
  - (*  ParenExpr *)
    inversion_clear H0; auto.
  - (*  UnExpr *)
      inversion_clear H0.
      destruct H with v0 S'2; auto. subst. auto.
  - (*  BinExpr *)
    inversion_clear H1.
    (*  Left operand*)
    assert (v1 = v3 /\ NatMap.Equal S' S'0). { auto. }
    destruct H1; subst.
    (*  Right operand *)
    assert (v2 = v4 /\ NatMap.Equal S'' S'2).
    { apply H0. apply S_Equal_EvalExpr with S'0; auto. symmetry. auto. }
    destruct H1; subst. auto.
  - (*  Local Assignment *)
    inversion_clear H0.
    + (*  Local assignment *)
      assert (z = v2 /\ NatMap.Equal S' S'0). { auto. }
      destruct H0. subst v2.
      assert (l0 = l). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst. rewrite <- H3 in e1. auto.
    + (*  Global assignment (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
  - (*  Global Assignment *)
    inversion_clear H0.
    + (*  Local assignment (contradiction) *)
      apply StringMap_mapsto_in in H1. contradiction.
    + (*  Global assignment *)
      assert (z = v2 /\ NatMap.Equal S' S'0). { auto. }
      destruct H0. subst v2.
      assert (l0 = l). { eapply StringMapFacts.MapsTo_fun; eauto. }
      subst. auto. rewrite <- H4 in e1. auto.
  -  (*  Function call *)
    inversion_clear H2.
    + (*  Function call *)
      assert ((params0, fstmt0, fexpr0) = (params, fstmt, fexpr)).
      { eapply StringMapFacts.MapsTo_fun; eauto. }
      inversion H2; subst params0 fstmt0 fexpr0; clear H2.
      assert (NatMap.Equal S' S'0 /\  es' = es'0). { auto. }
      destruct H2. subst es'0.

      assert (ls = ls0).
      { transitivity (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)); auto. }
      rewrite <- H14 in *; clear H14.
      assert (StringMap.Equal Ef Ef0).
      { transitivity (StringMapProperties.of_list (combine params ls)); auto; symmetry; auto. }
      assert (NatMap.Equal Sargs Sargs0).
      { transitivity (NatMapProperties.of_list (combine ls es')); auto; symmetry; auto. }
      assert (NatMap.Equal S'' S''0).
      { rewrite <- H2 in H10. rewrite <- H15 in H10.
      transitivity (NatMapProperties.update S' Sargs); auto; symmetry; auto. }

      apply S_Equal_EvalStmt with (S2:=S'') in H11; try symmetry; auto.
      apply E_Equal_EvalStmt with (E2:=Ef) in H11; try symmetry; auto.
      apply H0 in H11.
      apply S_Equal_EvalExpr with (S2:=S''') in H12; try symmetry; auto.
      apply E_Equal_EvalExpr with (E2:=Ef) in H12; try symmetry; auto.
      apply H1 in H12. destruct H12.
      rewrite <- H17 in H13. rewrite H13. rewrite e6. subst v2.
      split; reflexivity.
    + (*  Macro invocation (contradiction) *)
      apply StringMap_mapsto_in in H3. contradiction.
  - (*  Macro invocation *)
    inversion_clear H0.
    + (*  Function call (contradiction) *)
      apply StringMap_mapsto_in in m. contradiction.
    + (*  Macro invocation *)

      assert ((params0, mexpr0) = (params, mexpr)).
      { eapply StringMapFacts.MapsTo_fun; eauto. }
      inversion H0; subst params0 mexpr0; clear H0.

      assert (ls = ls0).
      { transitivity (seq (NatMap.cardinal (elt:=expr) S + 1) (Datatypes.length es)); auto. }
      rewrite <- H0 in *; clear H0.
      assert (StringMap.Equal Em Em0).
      { transitivity (StringMapProperties.of_list (combine params ls)); auto; symmetry; auto. }
      assert (NatMap.Equal Sargs Sargs0).
      { transitivity (NatMapProperties.of_list (combine ls es)); auto; symmetry; auto. }
      assert (NatMap.Equal S' S'0).
      { rewrite <- H10 in H6.
      transitivity (NatMapProperties.update S Sargs); auto; symmetry; auto. }
      assert (StringMap.Equal E' E'0).
      { rewrite H3 in H7. rewrite e0 in e3.
        transitivity (StringMapProperties.update E (StringMapProperties.of_list (combine params ls))); auto.
        symmetry; auto. }
      apply E_Equal_EvalExpr with (E2:=E') in H8; try symmetry; auto.
      apply S_Equal_EvalExpr with (S2:=S') in H8; try symmetry; auto.
      apply H in H8.
      destruct H8. subst v2. split; auto.
      rewrite <- H13 in H9.
      transitivity (NatMapProperties.restrict S'' S); auto; symmetry; auto.

  - inversion_clear H. transitivity S; auto; try symmetry; auto.
  - inversion_clear H0. apply H in H1. destruct H1; auto.
  - inversion_clear H1.
    + apply H in H2. destruct H2. apply S_Equal_EvalStmt with (S2:=S') in H4; symmetry; auto.
      apply H0 in H4. symmetry; auto.
    + apply H in H2. destruct H2. subst v0. contradiction.
  - inversion_clear H1.
    + apply H in H2. destruct H2. subst v0. contradiction.
    + apply H in H2. destruct H2. apply S_Equal_EvalStmt with (S2:=S') in H4; symmetry; auto.
      apply H0 in H4. symmetry; auto.
  - inversion_clear H0.
    + apply H with v0 S'2 in H1. destruct H1. auto.
    + apply H with v0 S'0 in H1. destruct H1. subst v0. contradiction.
  - inversion_clear H2.
    + apply H with v0 S'2 in H3; auto. destruct H3. subst v0. contradiction.
    + apply H with v0 S'0 in H3; auto. destruct H3. subst v0.
      apply S_Equal_EvalStmt with (S2:=S') in H5. 2 : { symmetry; auto. }
      apply H0 with S''0 in H5. apply H1. eapply S_Equal_EvalStmt; eauto.
      symmetry. auto.
  - inversion_clear H. transitivity S; auto. symmetry; auto.
  - inversion_clear H1. apply H in H2.
    apply S_Equal_EvalStmt with (S2:=S') in H3; auto; symmetry; auto.
  - inversion_clear H. split; auto. transitivity S; auto. rewrite e; reflexivity.
  - inversion_clear H1.
    apply H in H2. destruct H2. subst z0.
    apply S_Equal_EvalExprList with (S2:=S') in H3.
    apply H0 in H3. destruct H3. subst es'0. split; auto.
    symmetry. auto.
Qed.


Lemma EvalExprList_deterministic : forall S E G F M es S'1 es'1,
  EvalExprList S E G F M es S'1 es'1 ->
  forall S'2 es'2,
  EvalExprList S E G F M es S'2 es'2 ->
  NatMap.Equal S'1 S'2 /\ es'1 = es'2.
Proof.
  intros until es'1. intro H. induction H.
  - intros. inversion_clear H0. split; auto. transitivity S; auto; rewrite H; reflexivity.
  - intros. inversion_clear H1.
    apply EvalExpr_deterministic with (v1:=z) (S'1:=S') in H2; auto.
    destruct H2. subst z0. apply S_Equal_EvalExprList with (S2:=S') in H3; try symmetry; auto.
    apply IHEvalExprList in H3. destruct H3. subst es'0. split; auto.
Qed.
