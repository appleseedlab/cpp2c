(*  Transformations.v
    Definition of the transformation that Cpp2C performs as well as some
    lemmas concerning it
*)

Require Import
  Coq.FSets.FMapList
  Coq.Lists.List
  Coq.Strings.String
  ZArith.

From Cpp2C Require Import
  Syntax
  ConfigVars
  EvalRules
  SideEffects
  MapLemmas
  NoCallsFromFunctionTable
  NoMacroInvocations
  NoVarsInEnvironment.


Inductive TransformExpr :
  macro_table -> function_table -> expr ->
  function_table -> expr -> Prop :=

  | Transform_Num : forall M F z,
    (* Identity transformation *)
    TransformExpr M F (Num z) F (Num z)

  | Transform_Var : forall M F x,
    (* Identity transformation *)
    TransformExpr M F (Var x) F (Var x)

  | Transform_ParenExpr : forall M F e0 F' e0',
    (* Transform the inner expression *)
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (ParenExpr e0) F' (ParenExpr e0')

  | Transform_UnExpr : forall M F e0 F' e0' uo,
    (* Transform the inner expression *)
    TransformExpr M F e0 F' e0' ->
    TransformExpr M F (UnExpr uo e0) F' (UnExpr uo e0')

  | Transform_BinExpr : forall bo M F e1 e2 F' F'' F1result F2result e1' e2',

    (* Transform the left operand *)
    TransformExpr M F e1 F' e1' ->
    F' = StringMapProperties.update F F1result ->

    (* Transform the right operand *)
    TransformExpr M F' e2 F'' e2' ->
    F'' = StringMapProperties.update F' F2result ->

    (* What I find interesting here is what we *don't* need to add
       as premises in order for the proof to work *)

    (* e1 does not contain calls are to functions that were added
       while transforming e2 *)
    (* ExprNoCallsFromFunctionTable e1 F M F2result -> *)

    (* e1' does not contain calls to functions that were added
       while transforming e2 *)
    ExprNoCallsFromFunctionTable e1' F' M F2result ->

    (* e2 does not contain calls to functions that were added
       while transforming e1 *)
    ExprNoCallsFromFunctionTable e2 F M F1result ->

    (* e2' does not contain calls to functions that were added
       while transforming e1 *)
    (* ExprNoCallsFromFunctionTable e2' F'' M F1result -> *)

    TransformExpr M F (BinExpr bo e1 e2) F'' (BinExpr bo e1' e2')

  | Transform_Assign : forall M F x e F' e',
    TransformExpr M F e F' e' ->
    TransformExpr M F (Assign x e) F' (Assign x e')

  | Transform_FunctionCallTransformedNotExists :
    forall   F M x es F' F'' F''' F'''' es' newdef
             params fstmt fexpr fstmt' fexpr'
             Fesresult Fstmtresult Fexprresult,

    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->

    (* Transform function arguments *)
    TransformExprList M F es F' es' ->
    F' = StringMapProperties.update F Fesresult ->

    (* Transform function statement *)
    TransformStmt M F' fstmt F'' fstmt' ->
    F'' = StringMapProperties.update F' Fstmtresult ->

    (* Transform function return expression *)
    TransformExpr M F'' fexpr F''' fexpr' ->
    F''' =  StringMapProperties.update F'' Fexprresult ->

    (* Create the new definition of the function *)
    newdef = (params, fstmt', fexpr') ->

    (* es' does not contain calls to functions that
       were added while transforming fstmt or fexpr or
       the transformed function *)
    ExprListNoCallsFromFunctionTable es' F' M Fstmtresult ->
    ExprListNoCallsFromFunctionTable es' F'' M Fexprresult ->
    ExprListFunctionNotCalled es' F''' M x newdef ->

    (* fstmt' does not contain calls to functions that
       were added while transforming fexpr or the transformed function *)
    StmtNoCallsFromFunctionTable fstmt' F'' M Fexprresult ->
    StmtFunctionNotCalled fstmt' F''' M x newdef ->

    (* fexpr' does not contain a call to the transformed function or
       to functions that were added while transforming fstmt *)
    ExprFunctionNotCalled fexpr' F''' M x newdef ->

    (* fexpr does not contain calls to functions that were added
       while transforming fstmt or es *)
    ExprNoCallsFromFunctionTable fexpr F M Fstmtresult ->
    ExprNoCallsFromFunctionTable fexpr F' M Fstmtresult ->
    ExprNoCallsFromFunctionTable fexpr F M Fesresult ->

    (* fstmt does not contain calls to functions that were added
       while transforming es *)
    StmtNoCallsFromFunctionTable fstmt F M Fesresult ->

    (*  We have not already transformed this function *)
    (forall x',
      ~StringMap.MapsTo x' newdef F) ->

    (* Add the transformed function back to the function table under a new name *)
    F'''' = StringMapProperties.update F'''
      (StringMap.add x newdef (StringMap.empty function_definition)) ->

    TransformExpr M F (CallOrInvocation x es) F'''' (CallOrInvocation x es')

  (*  We try to transform a function, and find that the transformed
      function is the same and the untransformed function. In this case,
      we don't change the call *)
  | Transform_FunctionCallTransformedSameAsUntransformed :
    forall   F M x es F' F'' F''' es' newdef
             params fstmt fexpr fstmt' fexpr'
             Fesresult Fstmtresult Fexprresult,

    ~ StringMap.In x M ->
    StringMap.MapsTo x (params, fstmt, fexpr) F ->

    (* Transform function arguments *)
    TransformExprList M F es F' es' ->
    F' = StringMapProperties.update F Fesresult ->

    (* Transform function statement *)
    TransformStmt M F' fstmt F'' fstmt' ->
    F'' = StringMapProperties.update F' Fstmtresult ->

    (* Transform function return expression *)
    TransformExpr M F'' fexpr F''' fexpr' ->
    F''' =  StringMapProperties.update F'' Fexprresult ->

    (* Create the new definition of the function *)
    newdef = (params, fstmt', fexpr') ->

    (* es' does not contain calls to functions that
       were added while transforming fstmt or fexpr or
       the transformed function *)
    ExprListNoCallsFromFunctionTable es' F' M Fstmtresult ->
    ExprListNoCallsFromFunctionTable es' F'' M Fexprresult ->

    (* fstmt' does not contain calls to functions that
       were added while transforming fexpr or the transformed function *)
    StmtNoCallsFromFunctionTable fstmt' F'' M Fexprresult ->
    StmtFunctionNotCalled fstmt' F''' M x newdef ->

    (* fexpr' does not contain a call to the transformed function or
       to functions that were added while transforming fstmt *)
    ExprFunctionNotCalled fexpr' F''' M x newdef ->

    (*  es does not contain calls to functions that were added while
        transforming es, fstmt, or fexpr *)
    ExprListNoCallsFromFunctionTable es F M Fesresult ->
    ExprListNoCallsFromFunctionTable es F' M Fstmtresult ->
    ExprListNoCallsFromFunctionTable es F'' M Fexprresult ->

    (* fexpr does not contain calls to functions that were added
       while transforming fstmt or es *)
    ExprNoCallsFromFunctionTable fexpr F M Fstmtresult ->
    ExprNoCallsFromFunctionTable fexpr F' M Fstmtresult ->
    ExprNoCallsFromFunctionTable fexpr F M Fesresult ->
    ExprNoCallsFromFunctionTable fexpr F'' M Fexprresult ->

    (* fstmt does not contain calls to functions that were added
       while transforming es *)
    StmtNoCallsFromFunctionTable fstmt F M Fesresult ->

    (*  The transformed version of this function is identical
        to the untransformed version *)
    (es, fstmt, fexpr) = (es', fstmt', fexpr') ->

    (*  The original function name is not in any of the intermediate results *)
    ~ StringMap.In x Fesresult ->
    ~ StringMap.In x Fstmtresult ->
    ~ StringMap.In x Fexprresult ->

    (*  Note that we still update F. This is because the es, fstmt, or fexpr
        may be syntactically the same as their transformed counterparts,
        but may have involved function calls that needed to be transformed
        (see the previous case). This also covers the case where transforming
        the parts of the expression did not actually update F. *)
    TransformExpr M F (CallOrInvocation x es) F''' (CallOrInvocation x es)

  | Transform_MacroIdentity :
    forall F M x es params mexpr,

    (* TODO: Decide if we should recursively transform macros if one part
       of them makes the unable to be transformed.
       For now we don't transform them at all. *)

    StringMap.MapsTo x (params, mexpr) M ->

    (* We don't transform the macro if:
       - One of its arguments has side-effects
       - Its body has side-effects
       - Its body shares variables with its caller's environment
    *)
    Exists ExprHasSideEffects es \/
    ExprHasSideEffects mexpr \/
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x nil) v S' ->
      ~ ExprNoVarsInEnvironment mexpr E) ->

    TransformExpr M F (CallOrInvocation x es) F (CallOrInvocation x es)

  | Transform_FunctionLikeMacroBodyIsVarNoSharedVars1ArgNoSideEffects :
    forall F M x y p e e' F' fname newdef,

    StringMap.MapsTo x ((p::nil), (Var y)) M ->

    (*  e is a side-effect-free expression *)
    ~ ExprHasSideEffects e ->

    (* The macro's variable is not from its caller's environment *)
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x (e::nil)) v S' ->
      ExprNoVarsInEnvironment (Var y) E) ->

    (* Transform macro argument *)
    TransformExpr M F e F' e' ->

    (* Create the transformed definition *)
    newdef = ((p::nil), Skip, (Var y)) ->

    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F ->
    F' = StringMapProperties.update F (StringMap.add fname newdef (StringMap.empty function_definition)) ->

    TransformExpr M F (CallOrInvocation x (e::nil)) F' (CallOrInvocation fname (e::nil))


  | Transform_ObjectLikeMacroNoSideEffectsNoSharedVarsNoNestedMacros :
    forall F M x F' mexpr mexpr' fname newdef,

    StringMap.MapsTo x (nil, mexpr) M ->

    (* The macro does not have side-effects *)
    ~ ExprHasSideEffects mexpr ->
    (* The macro does not contain nested macro invocations *)
    ExprNoMacroInvocations mexpr F M ->

    (* The macro does not share variables with its caller's environment *)
    (forall S E G v S',
      EvalExpr S E G F M (CallOrInvocation x nil) v S' ->
      ExprNoVarsInEnvironment mexpr E) ->

    (* Transform macro body *)
    TransformExpr M F mexpr F' mexpr' ->

    (* Create the transformed definition *)
    newdef = (nil, Skip, mexpr') ->

    (* mexpr' does not contain a call to the transformed function *)
    ExprFunctionNotCalled mexpr' F' M x newdef ->

    (* Add the transformed function definition to the function table *)
    ~ StringMap.In fname M ->
    ~ StringMap.In fname F ->
    F' = StringMap.add fname newdef F ->

    TransformExpr M F (CallOrInvocation x nil) F' (CallOrInvocation fname nil)
with TransformExprList :
  macro_table -> function_table -> list expr ->
  function_table -> list expr -> Prop :=

  (* End of arguments *)
  | TransformExprList_Nil : forall M F,
    TransformExprList M F nil F nil

  (* There are arguments left to transform *)
  | TransformExprList_Cons : forall M F e es F' F'' e' es' Feresult Fesresult,
    (* Transform the first expression *)
    TransformExpr M F e F' e' ->
    F' = StringMapProperties.update F Feresult ->

    (* Transform the remaining expressions *)
    TransformExprList M F' es F'' es' ->
    F'' = StringMapProperties.update F' Fesresult ->

    (*  The transformed expression does not call any functions that
        were added while transforming the rest of the the expressions *)
    ExprNoCallsFromFunctionTable e' F' M Fesresult ->

    (*  None of the untransformed expressions called a function that was added
        while transforming the first expression *)
    ExprListNoCallsFromFunctionTable es F M Feresult ->

    TransformExprList M F (e::es) F'' (e'::es')
with TransformStmt :
  macro_table -> function_table -> stmt ->
  function_table -> stmt -> Prop :=

  | Transform_Skip : forall M F,
    TransformStmt M F Skip F Skip

  | Transform_Expr : forall M F e F' e',
    (*  Transform the inner expression *)
    TransformExpr M F e F' e' ->
    TransformStmt M F (Expr e) F' (Expr e')

  | Transform_If : forall M F cond s1 s2 F' F'' F''' cond' s1' s2' Fcondresult Fs1result Fs2result,
    (*  Transform the condition *)
    TransformExpr M F cond F' cond' ->
    F' = StringMapProperties.update F Fcondresult ->

    (*  Transform the true branch *)
    TransformStmt M F' s1 F'' s1' ->
    F'' = StringMapProperties.update F' Fs1result ->

    (*  Transform the false branch *)
    TransformStmt M F'' s2 F''' s2' ->
    F''' = StringMapProperties.update F'' Fs2result ->

    (*  The transformed condition does not call any functions
        that were added while transforming the true and false branches *)
    ExprNoCallsFromFunctionTable cond' F' M Fs1result ->
    ExprNoCallsFromFunctionTable cond' F'' M Fs2result ->

    (*  The original true branch does not call any functions that were added
        while transforming the condition, and the transformed true branch
        does not call any functions that were added while transforming the
        false branch *)
    StmtNoCallsFromFunctionTable s1 F M Fcondresult ->
    StmtNoCallsFromFunctionTable s1' F'' M Fs2result ->

    (*  The original false branch does not call any functions that were added
        while transforming the condition or true branch *)
    StmtNoCallsFromFunctionTable s2 F M Fcondresult ->
    StmtNoCallsFromFunctionTable s2 F' M Fs1result ->

    TransformStmt M F (IfElse cond s1 s2) F''' (IfElse cond' s1' s2')

  | Transform_While : forall M F cond s0 F' F'' cond' s0' Fcondresult Fs0result,
    (*  Transform the condition *)
    TransformExpr M F cond F' cond' ->
    F' = StringMapProperties.update F Fcondresult ->

    (*  Transform the body *)
    TransformStmt M F' s0 F'' s0' ->
    F'' = StringMapProperties.update F' Fs0result ->

    (*  The original condition does not call any function that were
        added while transforming the condition or while body, and
        the transformed condition does not call any functions that were
        added while transforming the while body *)
    ExprNoCallsFromFunctionTable cond F M Fcondresult ->
    ExprNoCallsFromFunctionTable cond F' M Fs0result ->
    ExprNoCallsFromFunctionTable cond' F' M Fs0result ->

    (*  The original while body does not call any functions that were added
        while transforming the condition or the while body *)
    StmtNoCallsFromFunctionTable s0 F M Fcondresult ->
    StmtNoCallsFromFunctionTable s0 F' M Fs0result ->

    (*  If we were to transform the original while loop again
        under the transformed function table, then we would get
        the same transformed condition and statement and not add
        any new functions to the function table *)
    TransformStmt M F'' (While cond s0) F'' (While cond' s0') ->

    TransformStmt M F (While cond s0) F'' (While cond' s0')

  | Transform_Compound_nil : forall M F,
    TransformStmt M F (Compound nil) F (Compound nil)

  | Transform_Compound_cons : forall M F s ss F' F'' s' ss' Fsresult Fssresult,
    (*  Transform first statement *)
    TransformStmt M F s F' s' ->
    F' = StringMapProperties.update F Fsresult ->

    (*  Transform the remaining statements *)
    TransformStmt M F' (Compound ss) F'' (Compound ss') ->
    F'' = StringMapProperties.update F' Fssresult ->

    (*  The transformed first statement does not call any functions
        that were added while transforming the remaining statements *)
    StmtNoCallsFromFunctionTable s' F' M Fssresult ->

    (*  The original remaining statement don't call any functions that
        were added while transforming the first statement *)
    StmtNoCallsFromFunctionTable (Compound ss) F M Fsresult ->

    TransformStmt M F (Compound (s::ss)) F'' (Compound (s'::ss')).


(*  Custom induction scheme *)
Scheme TransformExpr_mut := Induction for TransformExpr Sort Prop
with TransformExprList_mut := Induction for TransformExprList Sort Prop
with TransformStmt_mut := Induction for TransformStmt Sort Prop.


(*  If an expression does not contain any macro invocations, then
    after transformation it remains unchanged *)
Lemma TransformExpr_ExprNoMacroInvocations_e_eq : forall M F e F' e' ,
  TransformExpr M F e F' e' ->
  ExprNoMacroInvocations e F M ->
  e = e'.
Proof.
  apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
      ExprNoMacroInvocations e F M ->
      e = e')
    (* TransformExprList *)
    (fun M F es F' es' (h : TransformExprList M F es F' es') =>
      ExprListNoMacroInvocations es F M ->
      es = es')
    (* TransformStmt *)
    (fun M F s F' s' (h : TransformStmt M F s F' s') =>
      StmtNoMacroInvocations s F M ->
      s = s')
    ); intros; auto;
      try (solve [inversion_clear H0; f_equal; auto]);
      try (solve [inversion_clear H2; f_equal; subst; auto using
      StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations]);
      try (inversion_clear H0; apply StringMap_mapsto_in in m; contradiction).
  - (* BinExpr *)
    inversion_clear H1; subst; f_equal; auto using
      ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations.
  - (* ExprList *)
    inversion_clear H1. f_equal; auto.
    apply ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations with
      (F':=Feresult) in H3; auto. rewrite <- e0 in H3. auto.
  - inversion_clear H1. f_equal; auto. f_equal; auto.
    assert (Compound ss = Compound ss').
    { apply H0. rewrite e.
      apply StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations; auto. }
    inversion H1. auto.
Qed.


(*  If an expression does not contain macro invocations, then after
    transformation it does not contain macro invocations *)
Lemma TransformExpr_ExprNoMacroInvocations_ExprNoMacroInvocations : forall M F e F' e',
  TransformExpr M F e F' e' ->
  ExprNoMacroInvocations e F M ->
  ExprNoMacroInvocations e' F' M.
Proof.
  apply (TransformExpr_mut
    (* TransformExpr *)
    (fun M F e F' e' (h : TransformExpr M F e F' e') =>
      ExprNoMacroInvocations e F M ->
      ExprNoMacroInvocations e' F' M)
    (* TransformExprList *)
    (fun M F es F' es' (h : TransformExprList M F es F' es') =>
      ExprListNoMacroInvocations es F M ->
      ExprListNoMacroInvocations es' F' M)
    (* TransformStmt *)
    (fun M F s F' s' (h : TransformStmt M F s F' s') =>
      StmtNoMacroInvocations s F M ->
      StmtNoMacroInvocations s' F' M)); intros; auto;
        try (inversion_clear H0; solve [econstructor; eauto]);
        try (inversion_clear H0; apply StringMap_mapsto_in in m; contradiction);
        try (inversion_clear H1; constructor; subst; auto using
          ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations,
          StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations,
          ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations);
        try (inversion_clear H2; constructor; subst; auto using
          ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations,
          StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations,
          ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations).
  - (*  Function call (the transformed function does not already exist) *)
    inversion_clear H2.
    assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
    { apply StringMapFacts.MapsTo_fun with F x; auto. }
    inversion H2; subst params0 fstmt0 fexpr0; clear H2.
    apply NM_CallOrInvocation with params fstmt' fexpr'; subst; auto using
      ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations,
      StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations,
      ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations.
    + (* Prove that the function can actually be found in the transformed
         function table *)
      apply StringMapFacts.add_mapsto_iff.
      left. auto.
  - (*  Function call (the transformed function already exists) *)
    inversion e13; subst es' fstmt' fexpr'; clear e13.
    inversion_clear H2.
    assert ((params, fstmt, fexpr) = (params0, fstmt0, fexpr0)).
    { apply StringMapFacts.MapsTo_fun with F x; auto. }
    inversion H2; subst params0 fstmt0 fexpr0; clear H2.
    apply NM_CallOrInvocation with params fstmt fexpr; subst; auto using
      ExprNoMacroInvocations_update_ExprNoCallFromFunctionTable_ExprNoMacroInvocations,
      StmtNoMacroInvocations_update_StmtNoCallFromFunctionTable_StmtNoMacroInvocations,
      ExprListNoMacroInvocations_update_ExprListNoCallsFromFunctionTableExprList_ExprListNoMacroInvocations.
    apply StringMapProperties.update_mapsto_iff; right; split; auto.
    apply StringMapProperties.update_mapsto_iff; right; split; auto.
    apply StringMapProperties.update_mapsto_iff; right; split; auto.
Qed.
