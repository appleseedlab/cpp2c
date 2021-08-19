# Notes

## Steps

1) Collect basic macro data using SuperC
2) Collect more detailed data using Python script
3) Use Clang to analyze C AST for macro usage
4) Design/implement simple constant object macro conversion


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

## Other Notes
- Since macro definitions are all global in scope, don't have to worry about
  scoping rules.