# Transformation Tool
This directory contains the Clang plugin that transforms CPP macros into
C functions

<!--
NOTE TO SELF: DON'T TRY TO BUILD LLVM + CLANG FROM SOURCE IT DOESN'T WORK
-->

## Getting Started

### Prerequisites

- Clang 11
- LLVM 11
- Docker
- Cmake
- make

## Setting Up

NOTE: The following is based off of Dietrich's paper.

This version of the plugin has to be built with LLVM/CLang 11.
To ease your development setup, we provide a Docker container to build
and test the plugin:

-  Start the Docker container
  ```console
  # ./docker-container.sh
  ```
- Run `build.sh` to build the plugin and the wrapper
  ```console
  $ ./build.sh
  ```

## Run CPP To C

- From within the Docker container, run the wrapper script
  ```console
  $ ./build/bin/cpp-to-c -fsyntax-only ./tests/object_like_macro_body_literal_1.c
  ```

`-fsyntax-only` tells Clang not to compile the target file(s).
