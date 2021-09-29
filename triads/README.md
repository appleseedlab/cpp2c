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

## Adding Triads
If you would like to add a new triad file to this list,
please ensure that your file follow the file structure above.

You can use the script `preprocess.py` to automatically
preprocess the un-preprocessed code snippets in a triad file and write
them to the preprocessed code snippet of their corresponding triad to speed
up triad creation.
To use it, first ensure that you have set up Python virtual environment, e.g.
by running:

```bash
pipenv run
```

Next, open a shell in this directory and run:
```bash
python preprocess.py <triad_filename>
```

To preprocess a single file. Alternatively, you may run:
```bash
python preprocess.py -all
```
to preprocess all the triad files in this directory.