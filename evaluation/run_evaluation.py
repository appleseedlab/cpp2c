import os
import shutil
import subprocess
import sys
from collections import defaultdict
from typing import Dict, Set
from urllib.request import urlretrieve

import numpy as np

import clang_tools
import compile_command
from evaluation_programs import EVALUATION_PROGRAMS

CPP2C_PREFIX = 'CPP2C:'

MACRO_DEFINITION = 'Macro Definition'
MACRO_EXPANSION = 'Macro Expansion'
TRANSFORMED_DEFINITION = 'Transformed Definition'
TRANSFORMED_EXPANSION = 'Transformed Expansion'
UNTRANSFORMED_EXPANSION = 'Untransformed Expansion'

OBJECT_LIKE_PREFIX = 'ObjectLike'
FUNCTION_LIKE_PREFIX = 'FunctionLike'
EXTRACTED_EVALUATION_PROGRAMS_DIR = r'extracted_evaluation_programs/'

HYGIENE = 'Hygiene'
ENVIRONMENT_CAPTURE = 'Environment capture'
PARAMETER_SIDE_EFFECTS = 'Parameter side-effects'
UNSUPPORTED_CONSTRUCT = 'Unsupported construct'


def three_num(data):
    """90, 95, and 99th percentiles."""
    # Taken from Wikipedia
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [90, 95, 99], method='midpoint')


def five_num(data):
    """5xth percentiles."""
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [i for i in range(0, 101, 25)], method='midpoint')


def twenty_num(data):
    """5xth percentiles."""
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [i for i in range(0, 101, 5)], method='midpoint')


def is_system_header_path(path: str) -> bool:
    return '/usr/include' in path or '/usr/lib' in path


# Disable numpy text wrapping
np.set_printoptions(linewidth=np.inf)


def main():

    for evaluation_program in EVALUATION_PROGRAMS:

        # Download the program zip file if we do not already have it
        if not os.path.exists(evaluation_program.archive_file):
            print(
                f'Downloading {evaluation_program.name} from {evaluation_program.link_to_archive_file}')

            # Download the program's archive
            urlretrieve(evaluation_program.link_to_archive_file,
                        evaluation_program.archive_file)

        # Delete the old extracted archive
        shutil.rmtree(evaluation_program.extracted_archive_path,
                      ignore_errors=True)

        # Create a fresh extracted archive
        shutil.unpack_archive(
            evaluation_program.archive_file, evaluation_program.extract_dir)

        # Save the current directory so we can move back to it after
        # evaluating this program
        evaluation_dir = os.getcwd()

        # Configure program and generate compile_commands.json
        os.chdir(evaluation_program.extracted_archive_path)
        subprocess.run(evaluation_program.configure_compile_commands_script,
                       shell=True, capture_output=True)

        # Collect compile commands from compile_commands.json
        compile_commands = compile_command.load_compile_commands_from_file(
            'compile_commands.json')

        # Perform a dry run to count the number of unique expansions of
        # macros defined in the program
        hashes_of_macros_defined_in_program: Set[str] = set()
        macro_hashes_to_expansion_spelling_locations: Dict[str, Set[str]] = defaultdict(
            set)
        for cc in compile_commands:
            cmd = compile_command.cpp2c_command_from_compile_command(cc, [
                                                                     'tr', '-v'])
            # Change to the command directory to run the command
            os.chdir(cc.directory)
            cp = subprocess.run(cmd, shell=True,
                                capture_output=True, text=True)

            # Check if clang crashed
            if 'PLEASE' in cp.stderr:
                print(cp.stderr)
                exit(1)

            # Check for macro definitions and expansions
            for line in cp.stderr.splitlines():
                if line.startswith(f'CPP2C:{MACRO_DEFINITION}'):
                    _, mhash, spelling_location = line.split(',')
                    mname, mtype, mdef_path, mdef_num = mhash.split(';')
                    # Only consider macros which were defined in the source code,
                    # not those defined a system header or on the command line
                    if (not is_system_header_path(mdef_path) and
                            mdef_path != ''):
                        hashes_of_macros_defined_in_program.add(mhash)

                elif line.startswith(f'CPP2C:{MACRO_EXPANSION}'):
                    _, mhash, spelling_location = line.split(',')
                    if mhash in hashes_of_macros_defined_in_program:
                        macro_hashes_to_expansion_spelling_locations[mhash].add(
                            spelling_location)

        print(f'## {evaluation_program.name}')

        print(
            f'unique macro definitions: {len(hashes_of_macros_defined_in_program)}')
        print(
            f'unique expansions of macros defined: {sum(len(vs) for vs in macro_hashes_to_expansion_spelling_locations.values())}')

        # Transform the program to a fixpoint
        num_runs_to_fixpoint = 0
        while True:
            emitted_a_transformation = False
            for cc in compile_commands:
                cmd = compile_command.cpp2c_command_from_compile_command(
                    cc, ['tr', '-i', '-v'])
                cp = subprocess.run(cmd, shell=True,
                                    capture_output=True, text=True)

                # Check that clang didn't crash...
                if "PLEASE" in cp.stderr:
                    print(cp.stderr)
                    exit(1)

                for line in cp.stderr.splitlines():
                    if line.startswith(f'CPP2C:{TRANSFORMED_EXPANSION}'):
                        emitted_a_transformation = True

            num_runs_to_fixpoint += 1
            if not emitted_a_transformation:
                break
            print(
                f'finished run {num_runs_to_fixpoint} of {evaluation_program.name}', file=sys.stderr)

        print(f'runs to reach a fixpoint: {num_runs_to_fixpoint}')

        # Deduplicate transformed macros in all files
        for cc in compile_commands:
            cmd = compile_command.cpp2c_command_from_compile_command(
                cc, ['dd', '-i'])
            cp = subprocess.run(cmd, shell=True,
                                capture_output=True, text=True)
            # Check that clang didn't crash...
            if "PLEASE" in cp.stderr:
                print(cp.stderr)
                exit(1)

        # Count the number of unique transformed invocations

        # Key idea: Count the number of DeclRefExprs referencing
        # declarations coming from transformed macros
        # Obstacles:
        # - One macro may have many distinct transformed definitions
        #   spanning multiple files, each with a potentially different
        #   type signatures and
        # - If a macro contains nested invocations, then the transformed
        #   definition may end up containing transformed invocations.
        #   A macro may be transformed multiple times though, so we should
        #   only count the nested transformed invocations in one of the this
        #   macro's transformed definitions as uniquely transformed invocations.

        # Step 1: Collect all transformed declarations
        transformed_names_to_annotations: Dict[str, Dict] = {}
        for cc in compile_commands:
            transformed_names_to_annotations.update(
                clang_tools.collect_annotations_of_func_and_var_decls_emitted_by_cpp2c(cc))

        # Step 2: Search for unique transformed invocations

        # Define a function for hashing macros from an annotation

        def macro_hash_from_annotation(annotation: Dict) -> str:
            return (annotation['macro name'] + ";" +
                    annotation['macro type'] + ";" +
                    annotation['macro definition realpath'] + ";" +
                    str(annotation['macro definition number']))

        # Map each macro to a single transformed declaration under which to search
        # transformed invocations under
        seen_macro_hashes: Set[str] = set()
        canonical_transformed_decl_names: Set[str] = set()
        for name, annotation in transformed_names_to_annotations.items():
            mhash = macro_hash_from_annotation(annotation)
            if mhash not in seen_macro_hashes:
                canonical_transformed_decl_names.add(name)
                seen_macro_hashes.add(mhash)

        # Map each transformed decl name to its macro hash
        transformed_decl_names_to_macro_hashes = {
            name: macro_hash_from_annotation(annotation)
            for name, annotation in transformed_names_to_annotations.items()
        }

        macro_hash_to_unique_transformed_invocations: Dict[str, int] = defaultdict(
            int)
        for cc in compile_commands:
            hash_count_for_file = clang_tools.map_macro_hashes_to_unique_transformed_invocations(
                cc,
                transformed_decl_names_to_macro_hashes,
                canonical_transformed_decl_names)
            for mhash, count in hash_count_for_file.items():
                macro_hash_to_unique_transformed_invocations[mhash] += count

        print(
            f'transformed macros: {len(macro_hash_to_unique_transformed_invocations)}')

        unique_transformed_invocations = list(
            macro_hash_to_unique_transformed_invocations.values())

        num_unique_transformed_invocations = sum(
            unique_transformed_invocations)
        print(
            f'unique transformed invocations: {num_unique_transformed_invocations}')

        invocations_fivenum = five_num(unique_transformed_invocations)
        print(
            f'five point of unique transformed invocations: {invocations_fivenum}')

        invocations_twentynum = twenty_num(unique_transformed_invocations)
        print(
            f'twenty point of unique transformed invocations: {invocations_twentynum}')

        top_five_most_transformed_macros = [
            (mhash.split(';')[0], count)
            for mhash, count in sorted(
                macro_hash_to_unique_transformed_invocations.items(),
                reverse=True,
                key=lambda pair: pair[1])[0:5]]
        print(
            f'top five most transformed macros: {top_five_most_transformed_macros}')

        mhash_to_transformation_types: Dict[str, Set[str]] = defaultdict(set)
        for annotation in transformed_names_to_annotations.values():
            mhash = macro_hash_from_annotation(annotation)
            sig = annotation['transformed signature']
            mhash_to_transformation_types[mhash].add(sig)

        num_unique_types = [len(v)
                            for v in mhash_to_transformation_types.values()]

        types_fivenum = five_num(num_unique_types)
        print(f'five point of unique transformed types: {types_fivenum}')

        types_twentynum = twenty_num(num_unique_types)
        print(f'twenty point of unique transformed types: {types_twentynum}')

        top_five_macros_with_most_unique_types = [
            (mhash.split(';')[0], len(types))
            for mhash, types in sorted(
                mhash_to_transformation_types.items(),
                reverse=True,
                key=lambda pair: len(pair[1]))[0:5]]
        print(
            f'top five macros with most unique transformed types: {top_five_macros_with_most_unique_types}')

        sys.stdout.flush()

        print()

        # Change back to top-level evaluation directory
        os.chdir(evaluation_dir)


if __name__ == '__main__':
    main()
