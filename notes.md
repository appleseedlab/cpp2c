# Notes

## Link to Macro Classification Spreadsheet
https://docs.google.com/spreadsheets/d/105X24etCkwHLztrKJxefnnQZ2TOorseXEXw6lN8s2go/edit#gid=1535213954

## Steps

1) Collect basic macro data using Clang
2) Collect more detailed data using Python script
3) Use Clang to analyze C AST for macro usage
4) Design/implement simple constant object macro conversion
5) Design/implement simple pass-by-value function-like macro conversion

Rough data collection -> Fine data collection -> Rough classification
-> AST analysis -> Fine classification -> Conversion

## Mennie's Steps
1) Extract the code and macro facts
2) Choose the order in which to migrate each macro
3) Determine how each macro is being used
4) Generate a plan to transform each macro
5) Transform each macro

## Potential Pitfalls for Converting Simple Constant Object Macros
- What if the macro is defined multiple times? Can only assign to a const
  variable once.
  - Solution: Append two underscores and a number to the end of
    each subsequent definition.
      - Need to take care to replace the names of all macro uses correctly.
- What if a macro is defined multiple times under certain preprocessor
  conditionals?

- If a macro is used in a case label, need to convert it to an enum
  instead of a const.
    - Should group macros used in the same switch statement in the same enum.

- What about macros that use const variables or other simple constant macros
  in their bodies? Should these be converted as well?
  - For now no; eventually yes.

- Even for simple int types, need to figure the appropriate qualifiers,
  e.g., unsigned, long, short, etc.

## Suggested Types from https://dl.acm.org/doi/10.1145/1095430.1081712
- See Table 1 from the PDF

## Other Notes
- Since macro definitions are all global in scope, don't have to worry about
  scoping rules.
- How to best handle type conversion? Should the AST be analyzed to determine
  which type the user would prefer the macro be converted to?
- NOTE: pycparser can parse the following line as a binary op:
  ```
  a + b;
  ```
  It won't compile of course since the variables are undeclared,
  but maybe this can still be useful? Maybe infer the types of
  the operands from the AST, and then extract the variables
  into function parameters? Would be tricky but could conceivably work,
  so long as the macro doesn't rely on dynamic scoping. Then again,
  that case could be checked for by comparing all variable names found
  in the macro body to the parameter names in the macro definition.
- Other idea: for function-like macros, can just make return type and types
  of parameters void* for now until you can examine AST
- How should we handle macros that are defined in the file and
  used as static conditionals? For instance:
```c
#define CONDITION
#ifdef CONDITION
  // Some code
#endif
```
  This causes a problem because if we were to convert definitions of CONDITION 
  to constants, then the static conditional would not find CONDITION
  as being defined.

## Remember to Keep it Practical for Now
- We should do research to see how often potentially difficult-to-implement
  features such as dynamic scoping and referencing global variables are used
- It could be that such features are not often used by developers,
  so we can just focus on converting simple constant object macros
  and functions that don't reference variables from outer scopes for now

## The Eta Rule
- Eta reduction:      `\x -> f x` to `f`
- Eta abstraction:    `f` to `\x -> f x`
- Eta conversion:     Either one of the above