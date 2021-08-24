# Notes

## Steps

1) Collect basic macro data using SuperC
2) Collect more detailed data using Python script
3) Use Clang to analyze C AST for macro usage
4) Design/implement simple constant object macro conversion

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