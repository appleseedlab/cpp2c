# Cpp2C

## Table of Contents
- [Cpp2C](#cpp2c)
	- [Table of Contents](#table-of-contents)
	- [Implementation](#implementation)
		- [Prerequisites](#prerequisites)
		- [Setting Up](#setting-up)
		- [Run cpp2c](#run-cpp2c)
			- [Commands and Options](#commands-and-options)
		- [Testing](#testing)
	- [Evaluation](#evaluation)

## Implementation
The `implementation` directory contains the Clang plugin that transforms CPP macros into C functions.
To ease your development setup, we provide a Docker container to build and test the plugin:

### Prerequisites
- Clang 11
- LLVM 11
- Docker
- Cmake
- make

### Setting Up
cpp2c takes between 30 minutes to 1 hour to build.

-  Start the Docker container

	```console
	$ ./docker-container.sh
	```
-  Change directory to `implementation`

	```console
	$ cd implementation
	```
- Run `build.sh` to build the plugin and the wrapper script

	```console
	$ ./build.sh
	```

### Run cpp2c
From within the Docker container, run the wrapper script

```console
$ ./build/bin/cpp2c tr ./tests/hygiene.c
```

#### Commands and Options
cpp2c offers a variety of commands, each with their own set of options.
The syntax for calling cpp2c is:

```console
$ ./build/bin/cpp2c COMMAND {OPTION} C_FILE
```

Available commands and their respective options:
- `tr, transform`: Transforms macros to functions and variables.
  - `-i, --in-place`:	Edit files in place. Off by default.
  - `-v, --verbose`:	Emit all debug messages while transforming. Off by default.
  - `-shm, --standard-header-macros`:	Try to transform macros defined in standard headers. Off by default.
  - `-tce, --transform-conditional-evaluation`:	Transform macros containing conditional evaluation. Off by default. Warning - transforming these macros can introduce undefined behavior!
- `pa, print_annotations`:	Print all annotations in a file that were emitted by cpp2c.
- `ra, remove_annotations`
  - `-i, --in-place`:	Edit files in place. Off by default.

### Testing
cpp2c comes with a micro test suite, in the directory `implementation/tests`.
To run it, first build cpp2c, then run the script `run_tests.sh`:
```console
$ ./run_tests.sh
```

## Evaluation
After building cpp2c, see the readme in the `evaluation` directory for steps on running cpp2c's evaluation.