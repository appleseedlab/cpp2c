# Triads

This directory contains code "triads".

Each triad is composed of three versions of the same snippet of C code:
1. The un-preprocessed code.
2. The pre-processed code.
3. The way the code is expected to look after its macros have been converted
   to existing C constructs.

Each triad is stored as a YAML file to allow for programmatic access to its
contents.

Each triad file also contains the grammar used for identifying a macro's
corresponding AST fragment (e.g., a statement, expression, etc.).
The grammar is specified using
[EBNF notation](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form).

The C grammar is inspired by Jeff Lee's 1985
[Lex](https://www.lysator.liu.se/c/ANSI-C-grammar-l.html)
and
[Yacc](https://www.lysator.liu.se/c/ANSI-C-grammar-y.html)
specifications of the ANSI C grammar.

## Sample Triad File Structure
```yaml
grammar: |-
  ...

triads:
  - un-preprocessed: |-
      ...
    preprocessed: |-
      ...
    converted: |-
      ...
  - ...
```