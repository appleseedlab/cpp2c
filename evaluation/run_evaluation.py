import os
import shutil
import subprocess
import sys
from collections import defaultdict
from datetime import datetime
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

OBJECT_LIKE = 'object-like'
FUNCTION_LIKE = 'function-like'
EXTRACTED_EVALUATION_PROGRAMS_DIR = r'extracted_evaluation_programs/'

HYGIENE = 'Hygiene'
ENVIRONMENT_CAPTURE = 'Environment capture'
PARAMETER_SIDE_EFFECTS = 'Parameter side-effects'
UNSUPPORTED_CONSTRUCT = 'Unsupported construct'


def macro_hash_from_annotation(annotation: Dict) -> str:
    '''Given a Cpp2C annotation, returns its macro hash'''
    return (annotation['macro name'] + ";" +
            annotation['macro type'] + ";" +
            annotation['macro definition realpath'] + ";" +
            str(annotation['macro definition number']))


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
    return '/usr/include' in path or '/usr/lib' in path or '<scratch space>' in path or path == ''


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
        mhash_to_expansion_spellings_locs: Dict[str, Set[str]] = defaultdict(
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
                if line.startswith(f'CPP2C:{MACRO_EXPANSION}'):
                    _, mhash, spelling_location = line.split(',')
                    # fn, ln, cl = spelling_location.split(':')
                    # Only consider macros which were expanded in c or h files
                    # if fn.endswith('.c') or fn.endswith('.h'):
                    # Only consider macros which were expanded at least once
                    # and defined in the source code
                    mname, mtype, mdef_path, mdef_num = mhash.split(';')
                    if not is_system_header_path(mdef_path):
                        mhash_to_expansion_spellings_locs[mhash].add(
                            spelling_location)

        print(f'## {evaluation_program.name}')

        expanded_source_macros = mhash_to_expansion_spellings_locs.keys()

        print(
            f'unique expanded source macro definitions: {len(expanded_source_macros)}')
        print(
            f'    olms: {len([h for h in expanded_source_macros if OBJECT_LIKE in h])}')
        print(
            f'    flms: {len([h for h in expanded_source_macros if FUNCTION_LIKE in h])}')

        print(
            f'unique expansions of source macros: {sum(len(vs) for vs in mhash_to_expansion_spellings_locs.values())}')
        print(
            f'    olms: {sum(len(vs) for h, vs in mhash_to_expansion_spellings_locs.items() if OBJECT_LIKE in h)}')
        print(
            f'    flms: {sum(len(vs) for h, vs in mhash_to_expansion_spellings_locs.items() if FUNCTION_LIKE in h)}')

        # Transform the program to a fixpoint
        num_runs_to_fixpoint = 0
        start_time = datetime.now()
        # Record transformed macros
        transformed_mhashes: Set[str] = set()
        # While transforming, map each macro to its set of reasons why it wasn't transformed
        mhash_to_reasons_not_transformed: Dict[str, Set[str]] = defaultdict(
            set)
        while True:
            emitted_a_transformation = False
            for cc in compile_commands:
                cmd = compile_command.cpp2c_command_from_compile_command(
                    cc, ['tr', '-i', '-v'])
                # Change to the command directory to run the command
                os.chdir(cc.directory)
                cp = subprocess.run(cmd, shell=True,
                                    capture_output=True, text=True)

                # Check that clang didn't crash...
                if "PLEASE" in cp.stderr:
                    print(cp.stderr)
                    exit(1)

                for line in cp.stderr.splitlines():
                    if line.startswith(f'CPP2C:{TRANSFORMED_EXPANSION}'):
                        emitted_a_transformation = True
                        _, mhash, _, _ = line.split(',')
                        if mhash in expanded_source_macros:
                            transformed_mhashes.add(mhash)
                    elif line.startswith(f'CPP2C:{UNTRANSFORMED_EXPANSION}'):
                        _, mhash, _, reason = line.split(',')
                        if mhash in expanded_source_macros:
                            mhash_to_reasons_not_transformed[mhash].add(reason)

            num_runs_to_fixpoint += 1
            print(
                f'finished run {num_runs_to_fixpoint} of {evaluation_program.name}', file=sys.stderr)
            if not emitted_a_transformation:
                break
        end_time = datetime.now()
        elapsed = end_time - start_time
        print(
            f'time to reach a fixpoint: {elapsed.seconds}.{elapsed.seconds}s')

        print(f'runs to reach a fixpoint: {num_runs_to_fixpoint}')

        print(
            f'transformed source macros (based on Cpp2C messages): {len(transformed_mhashes)}')
        print(
            f'    olms: {len([h for h in transformed_mhashes if OBJECT_LIKE in h])}')
        print(
            f'    flms: {len([h for h in transformed_mhashes if FUNCTION_LIKE in h])}')

        # Remove from the list of untransformed macros those that were transformed at least once,
        # because a macro may have not been transformed in an early run and then transformed in
        # a later run
        # NOTE: We base this on the annotations seen while transforming, not while checking for
        # invocations
        untransformed_mhashes = {mhash for mhash
                                 in mhash_to_reasons_not_transformed
                                 if mhash not in transformed_mhashes}

        print(
            f'untransformed macros (based on Cpp2C messages): {len(untransformed_mhashes)}')
        print(
            f'    olms: {len([h for h in untransformed_mhashes if OBJECT_LIKE in h])}')
        print(
            f'    flms: {len([h for h in untransformed_mhashes if FUNCTION_LIKE in h])}')

        # Deduplicate transformed macros in all files
        # for cc in compile_commands:
        #     cmd = compile_command.cpp2c_command_from_compile_command(
        #         cc, ['dd', '-i'])
        #     # Change to the command directory to run the command
        #     os.chdir(cc.directory)
        #     cp = subprocess.run(cmd, shell=True,
        #                         capture_output=True, text=True)
        #     # Check that clang didn't crash...
        #     if "PLEASE" in cp.stderr:
        #         print(cp.stderr)
        #         exit(1)

        # Count the number of unique transformed invocations

        # Key idea: Count the number of DeclRefExprs referencing
        # declarations coming from transformed macros
        # Obstacles:
        # - One macro may have many distinct transformed definitions
        #   spanning multiple files, each with a potentially different
        #   type signature
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

        # Map each macro to a single transformed declaration under which to search
        # transformed invocations under
        seen_mhashes: Set[str] = set()
        canonical_transformed_decl_names: Set[str] = set()
        for name, annotation in transformed_names_to_annotations.items():
            mhash = macro_hash_from_annotation(annotation)
            if mhash not in seen_mhashes:
                seen_mhashes.add(mhash)
                canonical_transformed_decl_names.add(name)

        # Map each transformed decl name to its macro hash
        transformed_name_to_mhash = {
            name: macro_hash_from_annotation(annotation)
            for name, annotation in transformed_names_to_annotations.items()
        }

        macro_hash_to_unique_transformed_invocations: Dict[str, int] = defaultdict(
            int)
        macro_hash_to_unique_transformed_invocations_olms: Dict[str, int] = defaultdict(
            int)
        macro_hash_to_unique_transformed_invocations_flms: Dict[str, int] = defaultdict(
            int)
        for cc in compile_commands:
            hash_count_for_file = clang_tools.map_macro_hashes_to_unique_transformed_invocations(
                cc,
                transformed_name_to_mhash,
                canonical_transformed_decl_names)
            for mhash, count in hash_count_for_file.items():
                macro_hash_to_unique_transformed_invocations[mhash] += count
                if OBJECT_LIKE in mhash:
                    macro_hash_to_unique_transformed_invocations_olms[mhash] += count
                elif FUNCTION_LIKE in mhash:
                    macro_hash_to_unique_transformed_invocations_flms[mhash] += count

        # print(
        #     f'transformed macros (based on found transformed invocations): {len(macro_hash_to_unique_transformed_invocations)}')
        # print(
        #     f'    olms: {len(macro_hash_to_unique_transformed_invocations_olms)}')
        # print(
        #     f'    flms: {len(macro_hash_to_unique_transformed_invocations_flms)}')

        # print(
        #     f'difference: {set(transformed_mhashes).difference(set(macro_hash_to_unique_transformed_invocations.keys()))}')

        unique_transformed_invocations = list(
            macro_hash_to_unique_transformed_invocations.values())
        unique_transformed_invocations_olms = list(
            macro_hash_to_unique_transformed_invocations_olms.values())
        unique_transformed_invocations_flms = list(
            macro_hash_to_unique_transformed_invocations_flms.values())

        print(
            f'unique transformed invocations: {sum(unique_transformed_invocations)}')
        print(
            f'    olms: {sum(unique_transformed_invocations_olms)}')
        print(
            f'    flms: {sum(unique_transformed_invocations_flms)}')

        print(
            f'five point of unique transformed invocations: {five_num(unique_transformed_invocations)}')
        print(f'    olms: {five_num(unique_transformed_invocations_olms)}')
        print(f'    flms: {five_num(unique_transformed_invocations_flms)}')

        print(
            f'twenty point of unique transformed invocations: {twenty_num(unique_transformed_invocations)}')
        print(f'    olms: {twenty_num(unique_transformed_invocations_olms)}')
        print(f'    flms: {twenty_num(unique_transformed_invocations_flms)}')

        # FIX!

        top_five_most_transformed_macros = [
            (h.split(';')[0], count)
            for h, count in sorted(
                macro_hash_to_unique_transformed_invocations.items(),
                reverse=True,
                key=lambda pair: pair[1])[0:5]]

        top_five_most_transformed_olms = [
            (h.split(';')[0], count)
            for h, count in sorted(
                macro_hash_to_unique_transformed_invocations_olms.items(),
                reverse=True,
                key=lambda pair: pair[1])[0:5]]

        top_five_most_transformed_flms = [
            (h.split(';')[0], count)
            for h, count in sorted(
                macro_hash_to_unique_transformed_invocations_flms.items(),
                reverse=True,
                key=lambda pair: pair[1])[0:5]]

        print(
            f'top five most transformed macros: {top_five_most_transformed_macros}')
        print(f'    olms: {top_five_most_transformed_olms}')
        print(f'    flms: {top_five_most_transformed_flms}')

        mhash_to_transformation_types: Dict[str, Set[str]] = defaultdict(set)
        for annotation in transformed_names_to_annotations.values():
            mhash = macro_hash_from_annotation(annotation)
            sig = annotation['transformed signature']
            mhash_to_transformation_types[mhash].add(sig)

        num_unique_types = [len(v)
                            for v in mhash_to_transformation_types.values()]
        num_unique_types_olms = [len(v)
                                 for h, v in mhash_to_transformation_types.items()
                                 if OBJECT_LIKE in h]
        num_unique_types_flms = [len(v)
                                 for h, v in mhash_to_transformation_types.items()
                                 if FUNCTION_LIKE in h]

        print(
            f'five point of unique transformed types: {five_num(num_unique_types)}')
        print(f'    olms: {five_num(num_unique_types_olms)}')
        print(f'    flms: {five_num(num_unique_types_flms)}')

        print(
            f'twenty point of unique transformed types: {twenty_num(num_unique_types)}')
        print(f'    olms: {twenty_num(num_unique_types_olms)}')
        print(f'    flms: {twenty_num(num_unique_types_flms)}')

        top_five_macros_with_most_unique_types = [
            (mhash.split(';')[0], len(types))
            for mhash, types in sorted(
                mhash_to_transformation_types.items(),
                reverse=True,
                key=lambda pair: len(pair[1]))[0:5]]

        top_five_olms_with_most_unique_types = [
            (mhash.split(';')[0], len(types))
            for mhash, types in sorted(
                [(h, ts) for h, ts in mhash_to_transformation_types.items()
                 if OBJECT_LIKE in h],
                reverse=True,
                key=lambda pair: len(pair[1]))[0:5]]

        top_five_flms_with_most_unique_types = [
            (mhash.split(';')[0], len(types))
            for mhash, types in sorted(
                [(h, ts) for h, ts in mhash_to_transformation_types.items()
                 if FUNCTION_LIKE in h],
                reverse=True,
                key=lambda pair: len(pair[1]))[0:5]]

        print(
            f'top five macros with most unique transformed types: {top_five_macros_with_most_unique_types}')
        print(f'    olms: {top_five_olms_with_most_unique_types}')
        print(f'    flms: {top_five_flms_with_most_unique_types}')

        sys.stdout.flush()

        print()

        # Change back to top-level evaluation directory
        os.chdir(evaluation_dir)


if __name__ == '__main__':
    main()
