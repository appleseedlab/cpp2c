Grammar
-----------------------------------------------------------------------

```
start               =   translation_unit;

translation_unit    =   declaration_list;

declaration_list    =   declaration
                    |   declaration, declaration_list;

declaration         =   'int', identifier, ';'
                    |   'int', identifier, '=', expr, ';';

identifier          =   ? A valid C identifier ?;

expr                =   constant
                    |   identifier;

constant            =   ? any C integer constant ?;
```

-----------------------------------------------------------------------
Transformation Steps
-----------------------------------------------------------------------

1) Choose an `expr` nonterminal `E` to transform.

2) Find a unique identifier that has not yet been used in the program.
   
   (If we were converting macros to C language constructs, we would
   use the macro's name)
   
   Let `ETA_NAME` be a nonterminal symbol that produces the chosen
   identifier.

3) Add a new declaration to the top of the program.
   
   This declaration would follow the second alternative of the
   `declaration` production.
   
   It would be composed of the symbols:
   'int', `ETA_NAME`, '=', `E`, ';'

4) Replace `E` in the original program with `ETA_NAME`.

-----------------------------------------------------------------------
Explanation
-----------------------------------------------------------------------

This transformation uses eta abstraction to guarantee that the
resulting transformation will be sound.

Informally, eta abstraction is the process of converting a function
`f` to `\x -> f x`, where `\x` defines a lambda expression that accepts
one parameter `x` as input and returns a call to `f`, with `x` passed
to it, as output.

Let `f x ident` be the function that binds a variable denoted by the
identifier `ident` to the value `x`.

So long as the value `x` does not induce side-effects (which it is
guaranteed not to for expressions in this grammar), we can perform
eta abstraction on `f` as follows:

`f x ident` -> `\x -> f x ident`

The value `x` is abstracted away before it is bound to `ident`.

This is essentially what we are doing in step 3.

We are abstracting the value of the chosen `expr` nonterminal `E`
by "binding" (assigning) it to a variable named `ETA_NAME`,
and then passing that value to the original "binding operation"
(C variable declaration and initialization) that `E` was located in.

So if a macro's expansion is recognized by this grammar, then its
expansion can be abstracted into a variable.

All its invocations in the unpreprocessed source code can then be
replaced with this variable, and by eta abstraction, the transformed
program will be semantically equivalent to the preprocessed one.