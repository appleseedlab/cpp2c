# Evaluation

## Table of Contents
- [Evaluation](#evaluation)
  - [Table of Contents](#table-of-contents)
  - [Prerequisites](#prerequisites)
  - [Getting Started](#getting-started)
  - [Running the Evaluation](#running-the-evaluation)

## Prerequisites
- All of the prerequisites for cpp2c
- Python 3.8+

## Getting Started
1. Build Cpp2C. Refer back to the readme in the top-level directory for instructions on how to do this.
2. Install `pipenv`
```bash
$ python3 -m pip install pipenv
```
3. Install Python dependencies
```bash
$ pipenv install
```

## Running the Evaluation
1. Run `pipenv shell`
2. Run `python3 run_evaluation.py`
   1. Optional: If you would like to run the evaluation with the `-tce` option active, run `python3 run_evaluation.py tce` instead.

The file `evaluation_programs.py` contains links to compressed versions of all programs included in the study, as well as scripts for building and testing them.
`run_evaluation.py` will download these programs, unzip, build them, and transform them with cpp2c.
The transformer emits diagnostic data while transforming the programs, and the evaluation script emits this data to a file in the `results` directory (or `results-tce` directory if the tce argument was passed).
