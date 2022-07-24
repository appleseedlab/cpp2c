# Cpp2C

## Table of Contents

- [Cpp2C](#cpp2c)
  - [Table of Contents](#table-of-contents)
  - [Proof](#proof)
  - [Implementation](#implementation)
  - [Transformation Tool](#transformation-tool)
  - [License](#license)

## Proof

[./proof_of_soundness](./proof_of_soundness)

There is a Makefile for building the .v files.

Theorems.v has the main transformation equivalence theorem.

## Implementation

See the `implementation` folder's readme

## Transformation Tool

`implementation` directory contains the Clang plugin that transforms CPP macros
into C functions. To ease your development setup, we provide a Docker container
to build and test the plugin:

<!--
NOTE TO SELF: DON'T TRY TO BUILD LLVM + CLANG FROM SOURCE IT DOESN'T WORK
-->

### Prerequisites

- Clang 11
- LLVM 11
- Docker
- Cmake
- make

### Setting Up

NOTE: The following is based off of Dietrich's paper.

This version of the plugin has to be built with LLVM/CLang 11.

-  Start the Docker container

	```console
	$ ./docker-container.sh
	```
-  Change directory to `implementation`

	```console
	$ cd implementation
	```
- Run `build.sh` to build the plugin and the wrapper

	```console
	$ ./build.sh
	```

### Run CPP To C

- From within the Docker container, run the wrapper script

	```console
  	$ ./build/bin/cpp2c tr ./tests/hygiene.c
  	```

## License

BSD 2-Clause License
