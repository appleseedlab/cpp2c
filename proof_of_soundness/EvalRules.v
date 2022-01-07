Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Cpp2C Require Import Syntax.
From Cpp2C Require Import ConfigVars.

Section EvalRules.

Open Scope Z_scope.

(* Right now, a term that fails to evaluate will simply get "stuck";
   i.e. it will fail to be reduced further.
   We do not provide any error messages, but I think we could add
   this later using a sum type. *)
Reserved Notation
  "[ S , E , G , F , M '|-' e '=>' v , S' ]"
  (at level 90, left associativity).
Reserved Notation
  "{ S , E , G , F , M '=[' s ']=>' S' }"
  (at level 91, left associativity).
Inductive exprevalR :
  state -> environment -> environment -> func_definitions -> macro_definitions ->
  expr ->
  Z -> state -> Prop :=
  (* Numerals evaluate to their integer representation and do not
     change the state *)
  | E_Num : forall S E G F M z,
    [S, E, G, F, M |- (Num z) => z, S]
  (* Variable lookup returns the variable's R-value
     and does not change the state *)
  | E_X_Local : forall S E G F M x l v,
    lookupE x E = Some l ->
    lookupS l S = Some v ->
    [S, E, G, F, M |- (X x) => v, S]
  (* Local variables shadow global variables, so only if a local
     variable lookup fails do we check the global environment *)
  | E_X_Global : forall S E G F M x l v,
    lookupE x E = None ->
    lookupE x G = Some l ->
    lookupS l S = Some v ->
    [S, E, G, F, M |- (X x) => v, S]
  (* Parenthesized expressions evaluate to themselves *)
  | E_ParenExpr : forall S E G F M e v S',
    [S, E, G, F, M |- e => v, S'] ->
    [S, E, G, F, M |- (ParenExpr e) => v, S']
  (* Unary expressions *)
  | E_UnExpr : forall S E G F M S' uo e v,
    [S, E, G, F, M |- e => v, S'] ->
    [S, E, G, F, M |- (UnExpr uo e) => ((unopToOp uo) v), S']
  (* Binary expressions *)
  (* NOTE: Evaluation rules do not handle operator precedence.
     The parser must use a concrete syntax to generate a parse tree
     with the appropriate precedence levels in it. *)
  | E_BinExpr : forall S E G F M bo e1 e2 S' v1 S'' v2 S''',
    [S, E, G, F, M |- e1 => v1, S'] ->
    [S', E, G, F, M |- e2 => v2, S''] ->
    [S'', E, G, F, M |- (BinExpr bo e1 e2) =>
      (((binopToOp bo) v1 v2)), S''']
  (* Variable assignments update the store by adding a new L-value to
     R-value mapping or by overriding an existing one.
     The R-value is returned along with the updated state *)
  | E_Assign_Success : forall S E G F M l x e v S',
    [S, E, G, F, M |- e => v, S'] ->
    lookupE x E = Some l ->
    [S, E, G, F, M |- (Assign x e) => v, (l,v)::S']
  (* For function calls, we perform the following steps:
     1) Evaluate arguments
     2) Map parameters to arguments in function local environment,
        which is based on the global environment
     3) Evaluate the function's statement
     4) Evaluate the function's return expression
     5) Return the return value and store *)
  | E_FunctionCall: forall S E G F M x es params fstmt fexpr S' v S'',
    (* How to express argument evaluation? *)
    (* Define separate relation for evaluating a *list* of expressions.
       New inputs:  es (list of expressions)
                    vs (list of values evaluated so far)
                    ls (list of l-values created so far)
       Output:  vs (list of values that each e evaluates to)
                ls (list of l values that each v will map to)
       Next create the environment for function evaluation
       New inputs:  vs (list of values)
                    ls (list of l values)
                    params (list of parameters (strings))
       Output:  E (a new environment in which each param is mapped to
                  a *fresh* l-value from ls, each of which are
                  not already present in S')
                S' (a new store in which each fresh l-value is mapped
                   to the v corresponding to its param in E)
       Finally evaluate the function's statement and expression under
       the new E and S
    *)
    definition F x = Some (params, fstmt, fexpr) ->
    {S, nil, G, F, M =[ fstmt ]=> S'} ->
    [S', nil, G, F, M |- fexpr => v, S''] ->
    [S, E, G, F, M |- (CallOrInvocation x es) => v, S'']
  (* Macro invocation*)
  (* How to handle macro function name shadowing? *)
  (* How to handle nested macros? *)
  (* How to implement call-by-name? Could use thunks, but
     that would require pointers and could get messy... *)
  | E_MacroInvocation : forall S E G F M x es params mexpr v S',
    invocation M x = Some (params, mexpr) ->
    [S, E, G, F, M |- mexpr => v, S'] ->
    [S, E, G, F, M |- (CallOrInvocation x es) => v, S']
  where "[ S , E , G , F , M '|-' e '=>' v , S' ]" :=
    (exprevalR S E G F M e v S')
with arglistevalR :
  state -> environment -> environment -> func_definitions -> macro_definitions ->
  list expr -> list Z -> list nat ->
  list Z -> list nat -> Prop :=
  (* End of an argument list.
     We don't need to evaluate any more arguments or create any more
     l-value mappings for them *)
  | E_ArgListEmpty : forall S E G F M vs ls,
    arglistevalR S E G F M nil vs ls vs ls
  (* Non-empty expression list.
     We need evaluate the given argument and add the result and a new
     l-value mapping to the output. *)
  | E_ArgListNotEmpty :
    forall S E G F M (es: list expr)
           v l e erst vs vs' vs'' ls ls' ls'' S',
    es = (e::erst) ->
    (* Evaluate the argument *)
    [S, E, G, F, M |- e => v, S'] ->
    (* Create a fresh l-value. We assert that the l-value is not
       already in the list we are constructing; later we assert that
       none of these l-values are used in the store. *)
    nodup eq_nat_dec (l::ls) = (l::ls) ->
    ls' = (l::ls) ->
    vs' = (v::vs) ->
    arglistevalR S' E G F M erst vs' ls' vs'' ls'' ->
    arglistevalR S E G F M es vs ls vs'' ls''
with stmtevalR :
  state -> environment -> environment -> func_definitions -> macro_definitions ->
  stmt ->
  state -> Prop :=
  (* A skip statement does not change the state *)
  | E_Skip : forall S E G F M,
    {S, E, G, F, M =[ Skip ]=> S}
  (* An expression statement evaluates its expression and returns 
     the resulting state *)
  | E_ExprStmt : forall S E G F M e v S',
    [S, E, G, F, M |- e => v, S'] ->
    {S, E, G, F, M =[ ExprStmt e ]=> S'}
  (* An empty compound statement evaluates to its initial state *)
  | E_CompoundStatementEmpty : forall S E G F M,
    {S, E, G, F, M =[ CompoundStmt nil ]=> S}
  (* A non-empty compound statement evaluates its first statement and
     then the following statements *)
  | E_CompoundStatementNotEmpty : forall S E G F M stmts s0 rst S' S'',
    stmts = (s0::rst) ->
    {S, E, G, F, M =[ s0 ]=> S'} ->
    {S', E, G, F, M =[ CompoundStmt rst ]=> S''} ->
    {S, E, G, F, M =[ CompoundStmt stmts ]=> S''}
  (* An if statement whose condition evaluates to false only carries
     over the side-effects induced by evaluating its condition *)
  | E_IfFalse: forall S E G F M e s0 S',
    [S, E, G, F, M |- e => 0, S'] ->
    {S, E, G, F, M =[ IfStmt e s0 ]=> S'}
  (* An if statement whose condition evaluates to true carries over
     the side-effects from evaluating its condition and its statement *)
  | E_IfTrue: forall S E G F M e s0 v S' S'',
    v <> 0 ->
    [S, E, G, F, M |- e => v, S'] ->
    {S',E, G, F, M =[ s0 ]=> S''} ->
    {S, E, G, F, M =[ IfStmt e s0 ]=> S''}
  (* Side-effects from condition and false branch *)
  | E_IfElseFalse: forall S E G F M e s0 s1 S' S'',
    [S, E, G, F, M |- e => 0, S'] ->
    {S',E, G, F, M =[ s1 ]=> S''} ->
    {S, E, G, F, M =[ IfElseStmt e s0 s1 ]=> S''}
  (* Side-effects from condition and true branch *)
  | E_IfElseTrue: forall S E G F M e s0 s1 v S' S'',
    v <> 0 ->
    [S, E, G, F, M |- e => v, S'] ->
    {S', E, G, F, M =[ s0 ]=> S''} ->
    {S, E, G, F, M =[ IfElseStmt e s0 s1 ]=> S''}
  (* Similar to E_IfFalse *)
  | E_WhileFalse: forall S E G F M e s0 S',
    [S, E, G, F, M |- e => 0, S'] ->
    {S, E, G, F, M =[ WhileStmt e s0 ]=> S'}
  (* A while statement whose condition evaluates to false must be
     run again after evaluating its body *)
  | E_WhileTrue: forall S E G F M e s0 v S' S'' S''',
    v <> 0 ->
    [S, E, G, F, M |- e => v, S'] ->
    {S', E, G, F, M =[ s0 ]=> S''} ->
    {S'', E, G, F, M =[ WhileStmt e s0 ]=> S'''} ->
    {S, E, G, F, M =[ WhileStmt e s0 ]=> S'''}
  where "{ S , E , G , F , M '=[' s ']=>' S' }" :=
    (stmtevalR S E G F M s S').

Close Scope Z_scope.

End EvalRules.