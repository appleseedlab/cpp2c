import csv
import os
import shutil
import sys
from collections import deque
from dataclasses import astuple, dataclass, fields
from subprocess import CompletedProcess, run
from sys import stderr
from typing import Deque, Dict, List
from urllib.request import urlretrieve

import numpy as np

CPP2C_PREFIX = 'CPP2C:'

MACRO_DEFINITION = 'Macro Definition'
MACRO_EXPANSION = 'Macro Expansion'
TRANSFORMED_DEFINITION = 'Transformed Definition'
TRANSFORMED_EXPANSION = 'Transformed Expansion'
UNTRANSFORMED_EXPANSION = 'Untransformed Expansion'

OBJECT_LIKE_PREFIX = 'ObjectLike'
FUNCTION_LIKE_PREFIX = 'FunctionLike'
EXTRACTED_EVALUATION_PROGRAMS_DIR = r'extracted_evaluation_programs/'
STATS_DIR = r'stats/'

HYGIENE = 'Hygiene'
ENVIRONMENT_CAPTURE = 'Environment capture'
PARAMETER_SIDE_EFFECTS = 'Parameter side-effects'
UNSUPPORTED_CONSTRUCT = 'Unsupported construct'

# TODO: To make this more accurate, we should perform both a dry run and an
# actual transformation per complete run of each program.
# This would remove the issue of intermediate spelling locations changing
# between transformations of compilation units

# Also we should not just be hashing macros by using their source text.
# We should also be incorporating the source file name and definition number.
# This would ensure that we consider two macros that have the same name
# and definition in spearate, or even the same, files to be unique.


@dataclass
class MacroDefinition:
    macro_hash: str
    definition_location: str
    run_no_found: int


@dataclass
class MacroExpansion:
    macro_hash: str
    spelling_location: str
    run_no_found: int


@dataclass
class TransformedDefinition:
    macro_hash: str
    transformed_type: str
    emitted_name: str
    run_no_emitted: int


@dataclass
class TransformedExpansion:
    macro_hash: str
    spelling_location: str
    name_of_function_spelled_in: str
    run_no_emitted: int


@dataclass
class UntransformedExpansion:
    macro_hash: str
    spelling_location: str
    name_of_function_spelled_in: str
    category: str
    reason: str
    run_no_reported: int


@dataclass
class EvaluationProgram:
    name: str
    link_to_archive_file: str
    src_dir: str
    configure_script: str

    @property
    def archive_file(self) -> str:
        return self.link_to_archive_file[self.link_to_archive_file.rfind(r'/')+1:]

    @property
    def extract_dir(self) -> str:
        return EXTRACTED_EVALUATION_PROGRAMS_DIR

    @property
    def extracted_archive_path(self) -> str:
        return os.path.join(EXTRACTED_EVALUATION_PROGRAMS_DIR, self.name)


def parse_cpp2c_message(msg: str) -> str:
    for line in csv.reader([msg], skipinitialspace=True):
        return line


def is_location_in_extracted_program_c_or_h_file(location: str) -> bool:
    file, line, col = location.split(':')
    return (
        location.startswith(EXTRACTED_EVALUATION_PROGRAMS_DIR) and
        (file.endswith('.c') or file.endswith('.h'))
    )


# Taken from Wikipedia
def three_num(data):
    """90, 95, and 99th percentiles."""
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [90, 95, 99], method='midpoint')


def twenty_num(data):
    """5xth percentiles."""
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [i for i in range(0, 101, 10)], method='midpoint')


def twenty_num(data):
    """5xth percentiles."""
    # To avoid errors when passing an empty array
    if not data:
        data = [0]
    return np.percentile(data, [i for i in range(0, 101, 5)], method='midpoint')


# Disable numpy text wrapping
np.set_printoptions(linewidth=np.inf)


def main():

    evaluation_programs = [
        EvaluationProgram(
            r'bc-1.07',
            r'https://mirrors.kernel.org/gnu/bc/bc-1.07.tar.gz',
            r'bc',
            r'bash configure'
        ),
        EvaluationProgram(
            r'gzip-1.10',
            r'https://gnu.mirror.constant.com/gzip/gzip-1.10.tar.gz',
            r'.',
            r'bash configure'
        ),
        EvaluationProgram(
            r'remind-03.04.02',
            r'https://dianne.skoll.ca/projects/remind/download/OLD/remind-03.04.02.tar.gz',
            r'src',
            r'bash configure'
        ),
        EvaluationProgram(
            r'lua-5.4.4',
            r'https://www.lua.org/ftp/lua-5.4.4.tar.gz',
            r'src',
            r''
        ),
        # EvaluationProgram(
        #     r'test',
        #     r'test.zip',
        #     r'.',
        #     r''
        # )
    ]

    shutil.rmtree(STATS_DIR, ignore_errors=True)
    os.makedirs(STATS_DIR, exist_ok=True)

    for evaluation_program in evaluation_programs:

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

        # Get the path to the source directory of the program
        src_dir = os.path.join(evaluation_program.extracted_archive_path,
                               evaluation_program.src_dir)

        # Gather program C source files
        program_c_files: Deque[str] = deque()
        for dirpath, dirname, filenames in os.walk(src_dir):
            for filename in filenames:
                filepath = os.path.join(dirpath, filename)
                if filepath.endswith('.c'):
                    program_c_files.append(filepath)

        # Configure program
        print(f'Configuring {evaluation_program.name}')
        temp = os.getcwd()
        os.chdir(evaluation_program.extracted_archive_path)
        run(evaluation_program.configure_script, shell=True, capture_output=True)
        os.chdir(temp)

        # Initiate the run of the program
        run_no = 0

        all_macro_definitions: List[MacroDefinition] = []
        all_macro_expansions: List[MacroExpansion] = []
        all_transformed_definitions: List[TransformedDefinition] = []
        all_transformed_expansions: List[TransformedExpansion] = []
        all_untransformed_top_level_expansions: List[UntransformedExpansion] = [
        ]

        # Collect the textually unique macro definitions in the source program
        hashes_of_run_1_macro_definitions_in_evaluation_program: Set[str] = set(
        )

        # Collect the set of expansions of macros defined in the source program
        run_1_expansions_of_macros_defined_in_evaluation_program = []

        # Count the number of unique original macro expansions
        # This includes, but does not duplicate, spelling locations
        # of nested macro expansions
        total_unique_original_expansions: int = 0
        total_unique_original_object_like_expansions: int = 0
        total_unique_original_function_like_expansions: int = 0

        # Transform program files until no more transformations are made
        while True:
            run_no += 1
            print(f'Run {run_no} of {evaluation_program.name}')

            emitted_a_transformation = False

            macro_expansions_found_this_run: List[MacroExpansion] = []
            macro_definitions_found_this_run: List[MacroDefinition] = []

            # Perform a dry run first so as to not interfere with spelling locations
            if run_no == 1:
                for c_file in program_c_files:

                    macro_definitions_found_in_this_translation_unit: List[MacroDefinition] = \
                        []
                    macro_expansions_found_in_this_translation_unit: List[MacroExpansion] = \
                        []

                    cp: CompletedProcess = run(
                        (
                            f'../implementation/build/bin/cpp2c {c_file} '
                            '-fsyntax-only -Wno-all '
                            '-Xclang -plugin-arg-cpp2c -Xclang -v'
                        ),
                        shell=True, capture_output=True, text=True)

                    for line in cp.stderr.splitlines():
                        if not line.startswith(CPP2C_PREFIX):
                            continue

                        # Skip the Cpp2C message prefix
                        msg = line[len(CPP2C_PREFIX):]

                        # Ignore first field since its indicates the type of message
                        constructor_fields = parse_cpp2c_message(msg)[1:]

                        if msg.startswith(MACRO_DEFINITION):
                            macro_definitions_found_in_this_translation_unit.append(
                                MacroDefinition(*constructor_fields, run_no))

                        elif msg.startswith(MACRO_EXPANSION):
                            macro_expansions_found_in_this_translation_unit.append(
                                MacroExpansion(*constructor_fields, run_no))
                        elif msg.startswith(TRANSFORMED_DEFINITION):
                            pass

                        elif msg.startswith(TRANSFORMED_EXPANSION):
                            pass

                        elif msg.startswith(UNTRANSFORMED_EXPANSION):
                            pass

                        else:
                            print(
                                'Found what appeared to be a CPP2C message, but was not', file=stderr)
                            print(line)
                            exit(1)

                    # Add what we found in this translation unit to what
                    # we found this run
                    macro_definitions_found_this_run.extend(
                        macro_definitions_found_in_this_translation_unit)
                    macro_expansions_found_this_run.extend(
                        macro_expansions_found_in_this_translation_unit)

                    hashes_of_run_1_macro_definitions_in_evaluation_program.update({
                        md.macro_hash for md in macro_definitions_found_in_this_translation_unit
                        if is_location_in_extracted_program_c_or_h_file(md.definition_location)
                    })

                    run_1_expansions_of_macros_defined_in_evaluation_program.extend([
                        me for me in macro_expansions_found_in_this_translation_unit
                        if me.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program
                    ])

            transformed_definitions_found_this_run: List[TransformedDefinition] = \
                []
            transformed_expansions_found_this_run: List[TransformedExpansion] = \
                []
            untransformed_top_level_expansions_found_this_run: List[UntransformedExpansion] = \
                []
            # Perform a wet run to actually change the files
            for c_file in program_c_files:
                transformed_definitions_found_in_this_translation_unit: List[TransformedDefinition] = \
                    []
                transformed_expansions_found_in_this_translation_unit: List[TransformedExpansion] = \
                    []
                untransformed_top_level_expansions_found_in_this_translation_unit: List[UntransformedExpansion] = \
                    []

                cp: CompletedProcess = run(
                    (
                        f'../implementation/build/bin/cpp2c {c_file} '
                        '-fsyntax-only -Wno-all '
                        '-Xclang -plugin-arg-cpp2c -Xclang -ow '
                        '-Xclang -plugin-arg-cpp2c -Xclang -v'
                    ),
                    shell=True, capture_output=True, text=True)

                emitted_a_transformation_for_this_file = False

                for line in cp.stderr.splitlines():
                    if not line.startswith(CPP2C_PREFIX):
                        continue

                     # Skip the Cpp2C message prefix
                    msg = line[len(CPP2C_PREFIX):]

                    # Ignore first field since its indicates the type of message
                    constructor_fields = parse_cpp2c_message(msg)[1:]

                    if msg.startswith(MACRO_DEFINITION):
                        pass

                    elif msg.startswith(MACRO_EXPANSION):
                        pass

                    elif msg.startswith(TRANSFORMED_DEFINITION):
                        transformed_definitions_found_in_this_translation_unit.append(
                            TransformedDefinition(*constructor_fields, run_no))

                    elif msg.startswith(TRANSFORMED_EXPANSION):
                        transformed_expansions_found_in_this_translation_unit.append(
                            TransformedExpansion(*constructor_fields, run_no))
                        emitted_a_transformation_for_this_file = True

                    elif msg.startswith(UNTRANSFORMED_EXPANSION):
                        untransformed_top_level_expansions_found_in_this_translation_unit.append(
                            UntransformedExpansion(*constructor_fields, run_no))

                    else:
                        print(
                            'Found what appeared to be a CPP2C message, but was not', file=stderr)
                        print(line)
                        exit(1)

                if emitted_a_transformation_for_this_file:
                    print(f'Emitted at least one transformation in {c_file}')

                emitted_a_transformation = emitted_a_transformation or emitted_a_transformation_for_this_file

                transformed_definitions_found_this_run.extend(
                    transformed_definitions_found_in_this_translation_unit)
                transformed_expansions_found_this_run.extend(
                    transformed_expansions_found_in_this_translation_unit)
                untransformed_top_level_expansions_found_this_run.extend(
                    untransformed_top_level_expansions_found_in_this_translation_unit)

            # Add what we found this run to the total
            all_macro_definitions.extend(
                macro_definitions_found_this_run)
            all_macro_expansions.extend(
                macro_expansions_found_this_run)
            all_transformed_definitions.extend(
                transformed_definitions_found_this_run)
            all_transformed_expansions.extend(
                transformed_expansions_found_this_run)
            all_untransformed_top_level_expansions.extend(
                untransformed_top_level_expansions_found_this_run)

            if not emitted_a_transformation:
                break

        total_unique_original_expansions = len({
            me.spelling_location
            for me in run_1_expansions_of_macros_defined_in_evaluation_program
        })
        total_unique_original_object_like_expansions = \
            len({
                me.spelling_location
                for me in run_1_expansions_of_macros_defined_in_evaluation_program
                if me.macro_hash.startswith(OBJECT_LIKE_PREFIX)
            })
        total_unique_original_function_like_expansions = \
            len({
                me.spelling_location
                for me in run_1_expansions_of_macros_defined_in_evaluation_program
                if me.macro_hash.startswith(FUNCTION_LIKE_PREFIX)
            })

        # Number of unique macro definitions
        total_unique_macro_definitions = \
            len(hashes_of_run_1_macro_definitions_in_evaluation_program)

        total_unique_object_like_macro_definitions = \
            len({mh for mh in hashes_of_run_1_macro_definitions_in_evaluation_program if mh.startswith(
                OBJECT_LIKE_PREFIX)})

        total_unique_function_like_macro_definitions =\
            len({mh for mh in hashes_of_run_1_macro_definitions_in_evaluation_program if mh.startswith(
                FUNCTION_LIKE_PREFIX)})

        # Map each original macro definition in the evaluation program
        # to the set of unique spelling locations it was expanded at
        hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations = {
            mh: set() for mh in hashes_of_run_1_macro_definitions_in_evaluation_program
        }
        for me in run_1_expansions_of_macros_defined_in_evaluation_program:
            hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations[me.macro_hash].add(
                me.spelling_location)
        three_point_summary_of_unique_invocations_per_definition = three_num(
            [len(unique_invocations)
             for unique_invocations in hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations.values()]
        )
        three_point_summary_of_unique_object_like_invocations_per_definition = three_num(
            [
                len(unique_invocations)
                for mh, unique_invocations in hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations.items()
                if mh.startswith(OBJECT_LIKE_PREFIX)
            ]
        )
        three_point_summary_of_unique_function_like_invocations_per_definition = three_num(
            [
                len(unique_invocations)
                for mh, unique_invocations in hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations.items()
                if mh.startswith(FUNCTION_LIKE_PREFIX)
            ]
        )

        all_expansions_of_macros_defined_in_evaluation_program = \
            [
                te for te in all_transformed_expansions
                if te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program
            ]

        # For a subsequent run, we only count transformations of expansions
        # inside the program's original functions, and inside unique
        # function definitions that we emitted in the previous run.
        # By "unique", we mean that we only include a single transformed definition per
        # transformed macro.
        # We exclude both duplicate polymorphic definitions and definitions
        # we emitted in prior runs
        hashes_of_macros_to_no_longer_check_for_transformed_expansions_in = set()
        names_of_functions_to_check_for_transformed_expansions_in = set()
        # The starting set of functions so search for transformed expansions in
        # is the set of functions originally defined in the program
        for te in all_expansions_of_macros_defined_in_evaluation_program:
            if te.run_no_emitted == 1:
                names_of_functions_to_check_for_transformed_expansions_in.add(
                    te.name_of_function_spelled_in)

        unique_transformed_expansions = []
        for i in range(1, run_no):
            # Add all expansions to our list of unique expansions which were found
            # in one of the function definitions that we confirmed were good to check in
            unique_transformations_found_this_round = []
            for te in all_expansions_of_macros_defined_in_evaluation_program:
                if te.run_no_emitted == i:
                    if te.name_of_function_spelled_in in names_of_functions_to_check_for_transformed_expansions_in:
                        unique_transformations_found_this_round.append(te)

            unique_transformed_expansions.extend(
                unique_transformations_found_this_round)

            # Get all functions we emitted this run
            functions_emitted_this_run: List[TransformedDefinition] = \
                [
                    td for td in all_transformed_definitions
                    if td.run_no_emitted == i
            ]

            # Exclude new definitions of transformed definitions we've already seen
            unique_functions_emitted_this_run: List[TransformedDefinition] = []
            for f in functions_emitted_this_run:
                if f.macro_hash not in hashes_of_macros_to_no_longer_check_for_transformed_expansions_in:
                    unique_functions_emitted_this_run.append(f)
                    hashes_of_macros_to_no_longer_check_for_transformed_expansions_in.add(
                        f.macro_hash)

            # Add the names of these new functions to the names of the
            # functions to check for new transformed expansions in
            names_of_new_functions_to_check_for_transformed_expansions_in = \
                {f.emitted_name for f in unique_functions_emitted_this_run}
            names_of_functions_to_check_for_transformed_expansions_in.update(
                names_of_new_functions_to_check_for_transformed_expansions_in)

        num_unique_transformed_expansions = len(unique_transformed_expansions)
        num_unique_object_like_transformed_expansions = len(
            [te for te in unique_transformed_expansions if te.macro_hash.startswith(OBJECT_LIKE_PREFIX)])
        num_unique_function_like_transformed_expansions = len(
            [te for te in unique_transformed_expansions if te.macro_hash.startswith(FUNCTION_LIKE_PREFIX)])

        # Map the hashes of each macro defined in the evaluation program to
        # the set of signatures for the definitions we emitted for it
        hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions = {
            mh: set() for mh in hashes_of_run_1_macro_definitions_in_evaluation_program
        }
        for td in all_transformed_definitions:
            if td.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program:
                hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions[td.macro_hash].add(
                    td.transformed_type)

        # Collect the hashes of macros defined in the evaluation program that
        # we emitted a transformed definition for
        hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once = \
            {
                mh for mh, sigs
                in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.items()
                if len(sigs) > 0
            }

        # Count of macros defined in the evaluation program that we emitted
        # a transformed definition for
        num_run_1_macro_definitions_transformed_at_least_once = \
            len(hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once)
        num_run_1_object_like_macro_definitions_transformed_at_least_once = \
            len({mh for mh in hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once if mh.startswith(
                OBJECT_LIKE_PREFIX)})
        num_run_1_function_like_macro_definitions_transformed_at_least_once = \
            len({mh for mh in hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once if mh.startswith(
                FUNCTION_LIKE_PREFIX)})

        three_point_summary_of_unique_function_signatures_per_transformed_definition = three_num(
            [
                len(sigs) for sigs in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.values()
                if len(sigs) > 0
            ]
        )
        three_point_summary_of_unique_function_signatures_per_transformed_object_like_definition = three_num(
            [
                len(sigs)
                for mh, sigs
                in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.items()
                if (
                    len(sigs) > 0 and
                    mh.startswith(OBJECT_LIKE_PREFIX)
                )
            ]
        )
        three_point_summary_of_unique_function_signatures_per_transformed_function_like_definition = three_num(
            [
                len(sigs)
                for mh, sigs
                in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.items()
                if (
                    len(sigs) > 0 and
                    mh.startswith(FUNCTION_LIKE_PREFIX)
                )
            ]
        )
        fivexth_summary_of_unique_function_signatures_per_transformed_definition = twenty_num(
            [
                len(sigs) for sigs in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.values()
                if len(sigs) > 0
            ]
        )
        fivexth_summary_of_unique_function_signatures_per_transformed_object_like_definition = twenty_num(
            [
                len(sigs)
                for mh, sigs
                in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.items()
                if (
                    len(sigs) > 0 and
                    mh.startswith(OBJECT_LIKE_PREFIX)
                )
            ]
        )
        fivexth_summary_of_unique_function_signatures_per_transformed_function_like_definition = twenty_num(
            [
                len(sigs)
                for mh, sigs
                in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.items()
                if (
                    len(sigs) > 0 and
                    mh.startswith(FUNCTION_LIKE_PREFIX)
                )
            ]
        )

        # Map the hash of each macro defined in the evaluation program that
        # we transformed at least once to its run 1 expansion spelling locations
        hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_expansion_spelling_locations = {
            mh: set() for mh in hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once
        }
        for me in run_1_expansions_of_macros_defined_in_evaluation_program:
            if me.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once:
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_expansion_spelling_locations[me.macro_hash].add(
                    me.spelling_location)

        # Map the hash of each macro defined in the evaluation program that
        # we transformed at least once to its unique transformed expansions
        hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program = {
            # NOTE: We don;t use spelling location here because we construct this set using transformations that are supposed to be unique at this point
            mh: list() for mh in hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once
        }
        for te in unique_transformed_expansions:
            hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program[
                te.macro_hash].append(te)

        three_point_summary_of_transformed_invocations_per_transformed_defintion = three_num(
            [
                len(unique_transformations) for unique_transformations in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program.values()
            ])
        three_point_summary_of_transformed_object_like_invocations_per_transformed_defintion = three_num(
            [
                len(unique_transformations)
                for mh, unique_transformations in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program.items()
                if mh.startswith(OBJECT_LIKE_PREFIX)
            ])
        three_point_summary_of_transformed_function_like_invocations_per_transformed_defintion = three_num(
            [
                len(unique_transformations)
                for mh, unique_transformations in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program.items()
                if mh.startswith(FUNCTION_LIKE_PREFIX)
            ])

        # Map the hash of each macro defined in the evaluation program that
        # we transformed at least once to the number of its unique expansions
        # that we did not transform
        hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed = {
            mh: int for mh in hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once
        }
        for mh in hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once:
            original_expansions = hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_expansion_spelling_locations[
                mh]
            transformed_expansions = hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program[
                mh]
            num_not_transformed = (
                len(original_expansions) -
                len(transformed_expansions))
            # Sanity check
            if num_not_transformed < 0:
                print(
                    f"Found more transformed expansions for '{mh}' than original expansions")
                print(original_expansions)
                print(transformed_expansions)
            hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed[
                mh] = num_not_transformed

        three_point_summary_of_not_transformed_invocations_per_transformed_defintion = three_num(
            list(hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.values())
        )

        three_point_summary_of_not_transformed_object_like_invocations_per_transformed_defintion = three_num(
            [
                num_not_transformed
                for mh, num_not_transformed in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.items()
                if mh.startswith(OBJECT_LIKE_PREFIX)
            ])

        three_point_summary_of_not_transformed_function_like_invocations_per_transformed_defintion = three_num(
            [
                num_not_transformed
                for mh, num_not_transformed in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.items()
                if mh.startswith(FUNCTION_LIKE_PREFIX)
            ])

        fivexth_summary_of_not_transformed_invocations_per_transformed_defintion = twenty_num(
            list(hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.values())
        )

        fivexth_summary_of_not_transformed_object_like_invocations_per_transformed_defintion = twenty_num(
            [
                num_not_transformed
                for mh, num_not_transformed in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.items()
                if mh.startswith(OBJECT_LIKE_PREFIX)
            ])

        fivexth_summary_of_not_transformed_function_like_invocations_per_transformed_defintion = twenty_num(
            [
                num_not_transformed
                for mh, num_not_transformed in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.items()
                if mh.startswith(FUNCTION_LIKE_PREFIX)
            ])

        # Count the number of transformed expansions found in run 1
        top_level_transformed_expansions_run_1 = [
            te for te in all_transformed_expansions
            if (
                te.run_no_emitted == 1 and
                te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program
            )
        ]
        top_level_object_like_transformed_expansions_run_1 = [
            te for te in all_transformed_expansions
            if (
                te.run_no_emitted == 1 and
                te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                te.macro_hash.startswith(OBJECT_LIKE_PREFIX)
            )
        ]
        top_level_function_like_transformed_expansions_run_1 = [
            te for te in all_transformed_expansions
            if (
                te.run_no_emitted == 1 and
                te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                te.macro_hash.startswith(FUNCTION_LIKE_PREFIX)
            )
        ]

        # Count untransformed expansions in run 1
        top_level_untransformed_expansions_run_1 = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program
                )
            ]
        top_level_untransformed_object_like_expansions_run_1 = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.macro_hash.startswith(OBJECT_LIKE_PREFIX)
                )
            ]
        top_level_untransformed_function_like_expansions_run_1 = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.macro_hash.startswith(FUNCTION_LIKE_PREFIX)
                )
            ]

        # Count untransformed expansions in run 1 due to hygiene
        top_level_untransformed_expansions_run_1_unhygienic = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == HYGIENE
                )
            ]
        top_level_untransformed_object_like_expansions_run_1_unhygienic = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == HYGIENE and
                    ute.macro_hash.startswith(OBJECT_LIKE_PREFIX)
                )
            ]
        top_level_untransformed_function_like_expansions_run_1_unhygienic = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == HYGIENE and
                    ute.macro_hash.startswith(FUNCTION_LIKE_PREFIX)
                )
            ]

        # Count untransformed expansions in run 1 due to environment capture
        top_level_untransformed_expansions_run_1_environment_capturing = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == ENVIRONMENT_CAPTURE
                )
            ]
        top_level_untransformed_object_like_expansions_run_1_environment_capturing = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == ENVIRONMENT_CAPTURE and
                    ute.macro_hash.startswith(OBJECT_LIKE_PREFIX)
                )
            ]
        top_level_untransformed_function_like_expansions_run_1_environment_capturing = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == ENVIRONMENT_CAPTURE and
                    ute.macro_hash.startswith(FUNCTION_LIKE_PREFIX)
                )
            ]

        # Count untransformed expansions in run 1 due to parameter side-effects
        top_level_untransformed_expansions_run_1_parameter_side_effects = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == PARAMETER_SIDE_EFFECTS
                )
            ]
        top_level_untransformed_object_like_expansions_run_1_parameter_side_effects = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == PARAMETER_SIDE_EFFECTS and
                    ute.macro_hash.startswith(OBJECT_LIKE_PREFIX)
                )
            ]
        top_level_untransformed_function_like_expansions_run_1_parameter_side_effects = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == PARAMETER_SIDE_EFFECTS and
                    ute.macro_hash.startswith(FUNCTION_LIKE_PREFIX)
                )
            ]

        # Count untransformed expansions in run 1 due to unsupported constructs
        top_level_untransformed_expansions_run_1_unsupported_construct = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == UNSUPPORTED_CONSTRUCT
                )
            ]
        top_level_untransformed_object_like_expansions_run_1_unsupported_construct = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == UNSUPPORTED_CONSTRUCT and
                    ute.macro_hash.startswith(OBJECT_LIKE_PREFIX)
                )
            ]
        top_level_untransformed_function_like_expansions_run_1_unsupported_construct = \
            [
                ute for ute in all_untransformed_top_level_expansions
                if (
                    ute.run_no_reported == 1 and
                    te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program and
                    ute.category == UNSUPPORTED_CONSTRUCT and
                    ute.macro_hash.startswith(FUNCTION_LIKE_PREFIX)
                )
            ]

        # Count the number of macro definitions which were never transformed
        hashes_of_never_transformed_macros_in_evaluation_program = \
            hashes_of_run_1_macro_definitions_in_evaluation_program - \
            {te.macro_hash for te in all_transformed_expansions}
        hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation: Dict[str, Set[str]] = {
            h: set()
            for h in hashes_of_never_transformed_macros_in_evaluation_program
        }
        num_never_transformed_macro_definitions_in_evaluation_program = len(
            hashes_of_never_transformed_macros_in_evaluation_program)
        num_never_transformed_object_like_macro_definitions_in_evaluation_program = len(
            {h for h in hashes_of_never_transformed_macros_in_evaluation_program if h.startswith(OBJECT_LIKE_PREFIX)})
        num_never_transformed_function_like_macro_definitions_in_evaluation_program = len(
            {h for h in hashes_of_never_transformed_macros_in_evaluation_program if h.startswith(FUNCTION_LIKE_PREFIX)})

        # Count the number of macro definitions that were never expanded for various reasons
        for ute in all_untransformed_top_level_expansions:
            if ute.macro_hash in hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation:
                hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation[ute.macro_hash].add(
                    ute.category)

        # Count the number of macro definitions that were never transformed only due to hygiene
        hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_hygiene = {
            h for h, cats in hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation.items()
            if cats == {HYGIENE}
        }
        num_never_transformed_definitions_only_due_to_hygiene = len(
            hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_hygiene)
        num_never_transformed_object_like_definitions_only_due_to_hygiene = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_hygiene
            if h.startswith(OBJECT_LIKE_PREFIX)
        })
        num_never_transformed_function_like_definitions_only_due_to_hygiene = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_hygiene
            if h.startswith(FUNCTION_LIKE_PREFIX)
        })
        # Count the number of macro definitions that were never transformed only due to environment capture
        hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_environment_capture = {
            h for h, cats in hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation.items()
            if cats == {ENVIRONMENT_CAPTURE}
        }
        num_never_transformed_definitions_only_due_to_environment_capture = len(
            hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_environment_capture)
        num_never_transformed_object_like_definitions_only_due_to_environment_capture = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_environment_capture
            if h.startswith(OBJECT_LIKE_PREFIX)
        })
        num_never_transformed_function_like_definitions_only_due_to_environment_capture = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_environment_capture
            if h.startswith(FUNCTION_LIKE_PREFIX)
        })
        # Count the number of macro definitions that were never transformed only due to parameter side-effects
        hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_parameter_side_effects = {
            h for h, cats in hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation.items()
            if cats == {PARAMETER_SIDE_EFFECTS}
        }
        num_never_transformed_definitions_only_due_to_parameter_side_effects = len(
            hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_parameter_side_effects)
        num_never_transformed_object_like_definitions_only_due_to_parameter_side_effects = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_parameter_side_effects
            if h.startswith(OBJECT_LIKE_PREFIX)
        })
        num_never_transformed_function_like_definitions_only_due_to_parameter_side_effects = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_parameter_side_effects
            if h.startswith(FUNCTION_LIKE_PREFIX)
        })
        # Count the number of macro definitions that were never transformed only due to unsupported constructs
        hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_unsupported_constructs = {
            h for h, cats in hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation.items()
            if cats == {UNSUPPORTED_CONSTRUCT}
        }
        num_never_transformed_definitions_only_due_to_unsupported_constructs = len(
            hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_unsupported_constructs)
        num_never_transformed_object_like_definitions_only_due_to_unsupported_constructs = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_unsupported_constructs
            if h.startswith(OBJECT_LIKE_PREFIX)
        })
        num_never_transformed_function_like_definitions_only_due_to_unsupported_constructs = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_unsupported_constructs
            if h.startswith(FUNCTION_LIKE_PREFIX)
        })
        # Count the number of macro definitions that were never transformed due to multiple reasons
        hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_multiple_reasons = {
            h for h, cats in hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation.items()
            if len(cats) > 1
        }
        num_never_transformed_definitions_only_due_to_multiple_reasons = len(
            hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_multiple_reasons)
        num_never_transformed_object_like_definitions_only_due_to_multiple_reasons = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_multiple_reasons
            if h.startswith(OBJECT_LIKE_PREFIX)
        })
        num_never_transformed_function_like_definitions_only_due_to_multiple_reasons = len({
            h for h in hashes_of_never_transformed_macros_in_evaluation_program_only_due_to_multiple_reasons
            if h.startswith(FUNCTION_LIKE_PREFIX)
        })
        
        
        # Count the number of macro definitions that were never transformed due to multiple reasons
        # NOTE: This counts macros that were never expanded in .c files;
        #       to count macros that were never expanded in any file, use the commented code below
        hashes_of_never_expanded_macro_definitions = {
            h for h, cats in hashes_of_never_transformed_macros_in_evaluation_program_to_categories_of_untransformation.items()
            if len(cats) == 0
        }
        num_never_expanded_macros = len(
            hashes_of_never_expanded_macro_definitions)
        num_never_expanded_object_like_macros = len({
            h for h in hashes_of_never_expanded_macro_definitions
            if h.startswith(OBJECT_LIKE_PREFIX)
        })
        num_never_expanded_function_like_macros = len({
            h for h in hashes_of_never_expanded_macro_definitions
            if h.startswith(FUNCTION_LIKE_PREFIX)
        })

        # # Count the number of macro definitions that were never expanded
        # hashes_of_never_expanded_macro_definitions = \
        #     hashes_of_run_1_macro_definitions_in_evaluation_program - \
        #     {me.macro_hash for me in run_1_expansions_of_macros_defined_in_evaluation_program}
        # num_never_expanded_macros = len(
        #     hashes_of_never_expanded_macro_definitions)
        # num_never_expanded_object_like_macros = len(
        #     {h for h in hashes_of_never_expanded_macro_definitions if h.startswith(OBJECT_LIKE_PREFIX)})
        # num_never_expanded_function_like_macros = len(
        #     {h for h in hashes_of_never_expanded_macro_definitions if h.startswith(FUNCTION_LIKE_PREFIX)})

        all_stats = {
            'program name': evaluation_program.name,
            '# of runs': run_no,
            'total unique definitions': total_unique_macro_definitions,
            'unique transformed definitions': num_run_1_macro_definitions_transformed_at_least_once,
            '# of unique definitions untransformed': num_never_transformed_macro_definitions_in_evaluation_program,
            '# of unique definitions untransformed only due to hygiene': num_never_transformed_definitions_only_due_to_hygiene,
            '# of unique definitions untransformed only due to environment capture': num_never_transformed_definitions_only_due_to_environment_capture,
            '# of unique definitions untransformed only due to parameter side-effects': num_never_transformed_definitions_only_due_to_parameter_side_effects,
            '# of unique definitions untransformed only due to unsupported constructs': num_never_transformed_definitions_only_due_to_unsupported_constructs,
            '# of unique definitions untransformed only due to multiple reasons': num_never_transformed_definitions_only_due_to_multiple_reasons,
            '# of unique definitions that were never expanded in a transformed file': num_never_expanded_macros,
            'total unique invocations': total_unique_original_expansions,
            'unique transformed invocations': num_unique_transformed_expansions,
            'unique not transformed invocations': total_unique_original_expansions - num_unique_transformed_expansions,
            '90-95-99 percentiles of unique invocations per definition': three_point_summary_of_unique_invocations_per_definition,
            '90-95-99 percentiles of not transformed invocations per transformed definition': three_point_summary_of_not_transformed_invocations_per_transformed_defintion,
            '5xth percentiles of not transformed invocations per transformed definition': fivexth_summary_of_not_transformed_invocations_per_transformed_defintion,
            '90-95-99 percentiles of transformed invocations per transformed definition': three_point_summary_of_transformed_invocations_per_transformed_defintion,
            '90-95-99 percentiles of unique function signatures per transformed definition': three_point_summary_of_unique_function_signatures_per_transformed_definition,
            '5xth percentiles of unique function signatures per transformed definition': fivexth_summary_of_unique_function_signatures_per_transformed_definition
        }

        olm_stats = {
            'program name': evaluation_program.name,
            '# of runs': run_no,
            'total unique definitions': total_unique_object_like_macro_definitions,
            'unique transformed definitions': num_run_1_object_like_macro_definitions_transformed_at_least_once,
            '# of unique definitions untransformed': num_never_transformed_object_like_macro_definitions_in_evaluation_program,
            '# of unique definitions untransformed only due to hygiene': num_never_transformed_object_like_definitions_only_due_to_hygiene,
            '# of unique definitions untransformed only due to environment capture': num_never_transformed_object_like_definitions_only_due_to_environment_capture,
            '# of unique definitions untransformed only due to parameter side-effects': num_never_transformed_object_like_definitions_only_due_to_parameter_side_effects,
            '# of unique definitions untransformed only due to unsupported constructs': num_never_transformed_object_like_definitions_only_due_to_unsupported_constructs,
            '# of unique definitions untransformed only due to multiple reasons': num_never_transformed_object_like_definitions_only_due_to_multiple_reasons,
            '# of unique definitions that were never expanded in a transformed file': num_never_expanded_object_like_macros,
            'total unique invocations': total_unique_original_object_like_expansions,
            'unique transformed invocations': num_unique_object_like_transformed_expansions,
            'unique not transformed invocations': total_unique_original_object_like_expansions - num_unique_object_like_transformed_expansions,
            '90-95-99 percentiles of unique invocations per definition': three_point_summary_of_unique_object_like_invocations_per_definition,
            '90-95-99 percentiles of not transformed invocations per transformed definition': three_point_summary_of_not_transformed_object_like_invocations_per_transformed_defintion,
            '5xth percentiles of not transformed invocations per transformed definition': fivexth_summary_of_not_transformed_object_like_invocations_per_transformed_defintion,
            '90-95-99 percentiles of transformed invocations per transformed definition': three_point_summary_of_transformed_object_like_invocations_per_transformed_defintion,
            '90-95-99 percentiles of unique function signatures per transformed definition': three_point_summary_of_unique_function_signatures_per_transformed_object_like_definition,
            '5xth percentiles of unique function signatures per transformed definition': fivexth_summary_of_unique_function_signatures_per_transformed_object_like_definition
        }

        flm_stats = {
            'program name': evaluation_program.name,
            '# of runs': run_no,
            'total unique definitions': total_unique_function_like_macro_definitions,
            'unique transformed definitions': num_run_1_function_like_macro_definitions_transformed_at_least_once,
            '# of unique definitions untransformed': num_never_transformed_function_like_macro_definitions_in_evaluation_program,
            '# of unique definitions untransformed only due to hygiene': num_never_transformed_function_like_definitions_only_due_to_hygiene,
            '# of unique definitions untransformed only due to environment capture': num_never_transformed_function_like_definitions_only_due_to_environment_capture,
            '# of unique definitions untransformed only due to parameter side-effects': num_never_transformed_function_like_definitions_only_due_to_parameter_side_effects,
            '# of unique definitions untransformed only due to unsupported constructs': num_never_transformed_function_like_definitions_only_due_to_unsupported_constructs,
            '# of unique definitions untransformed only due to multiple reasons': num_never_transformed_function_like_definitions_only_due_to_multiple_reasons,
            '# of unique definitions that were never expanded in a transformed file': num_never_expanded_function_like_macros,
            'total unique invocations': total_unique_original_function_like_expansions,
            'unique transformed invocations': num_unique_function_like_transformed_expansions,
            'unique not transformed invocations': total_unique_original_function_like_expansions - num_unique_function_like_transformed_expansions,
            '90-95-99 percentiles of unique invocations per definition': three_point_summary_of_unique_function_like_invocations_per_definition,
            '90-95-99 percentiles of not transformed invocations per transformed definition': three_point_summary_of_not_transformed_function_like_invocations_per_transformed_defintion,
            '5xth percentiles of not transformed invocations per transformed definition': fivexth_summary_of_not_transformed_function_like_invocations_per_transformed_defintion,
            '90-95-99 percentiles of transformed invocations per transformed definition': three_point_summary_of_transformed_function_like_invocations_per_transformed_defintion,
            '90-95-99 percentiles of unique function signatures per transformed definition': three_point_summary_of_unique_function_signatures_per_transformed_function_like_definition,
            '5xth percentiles of unique function signatures per transformed definition': fivexth_summary_of_unique_function_signatures_per_transformed_function_like_definition
        }

        # Dump transformable expansion stats

        all_stats_file = os.path.join(STATS_DIR, 'stats.csv')

        if not os.path.exists(all_stats_file):
            with open(all_stats_file, 'w') as ofp:
                print(','.join(all_stats.keys()), file=ofp)

        with open(all_stats_file, 'a') as ofp:
            # NOTE: this is safe to do since iterating a dict
            # in Python is consistent
            print(','.join([str(v) for v in all_stats.values()]), file=ofp)

        olm_stats_file = os.path.join(STATS_DIR, 'olm-stats.csv')

        if not os.path.exists(olm_stats_file):
            with open(olm_stats_file, 'w') as ofp:
                print(','.join(olm_stats.keys()), file=ofp)

        with open(olm_stats_file, 'a') as ofp:
            print(','.join([str(v)
                  for v in olm_stats.values()]), file=ofp)

        flm_stats_file = os.path.join(STATS_DIR, 'flm-stats.csv')

        if not os.path.exists(flm_stats_file):
            with open(flm_stats_file, 'w') as ofp:
                print(','.join(flm_stats.keys()), file=ofp)

        with open(flm_stats_file, 'a') as ofp:
            print(','.join([str(v)
                  for v in flm_stats.values()]), file=ofp)

        # Print hashes of transformed macros with number of signatures emitted
        signature_stats_file = os.path.join(
            STATS_DIR, f'signature-stats-{evaluation_program.name}.csv')
        with open(signature_stats_file, 'w') as ofp:
            print('macro hash, number of unique transformed signatures', file=ofp)
            for mh, sigs in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.items():
                if len(sigs) > 0:
                    print(mh + ',' + str(len(sigs)), file=ofp)

        # # Dump untransformable expansion stats

        # run_1_untransformed_top_level_stats = {
        #     'program name': evaluation_program.name,
        #     'unhygienic': len(top_level_untransformed_expansions_run_1_unhygienic),
        #     'environment capturing': len(top_level_untransformed_expansions_run_1_environment_capturing),
        #     'parameter side-effects': len(top_level_untransformed_expansions_run_1_parameter_side_effects),
        #     'unsupported constructs': len(top_level_untransformed_expansions_run_1_unsupported_construct),
        #     'total untransformed': len(top_level_untransformed_expansions_run_1),
        #     'total transformed': len(top_level_transformed_expansions_run_1)
        # }

        # run_1_untransformed_top_level_olm_stats = {
        #     'program name': evaluation_program.name,
        #     'unhygienic': len(top_level_untransformed_object_like_expansions_run_1_unhygienic),
        #     'environment capturing': len(top_level_untransformed_object_like_expansions_run_1_environment_capturing),
        #     'parameter side-effects': len(top_level_untransformed_object_like_expansions_run_1_parameter_side_effects),
        #     'unsupported constructs': len(top_level_untransformed_object_like_expansions_run_1_unsupported_construct),
        #     'total': len(top_level_untransformed_object_like_expansions_run_1),
        #     'total transformed': len(top_level_object_like_transformed_expansions_run_1)
        # }

        # run_1_untransformed_top_level_flm_stats = {
        #     'program name': evaluation_program.name,
        #     'unhygienic': len(top_level_untransformed_function_like_expansions_run_1_unhygienic),
        #     'environment capturing': len(top_level_untransformed_function_like_expansions_run_1_environment_capturing),
        #     'parameter side-effects': len(top_level_untransformed_function_like_expansions_run_1_parameter_side_effects),
        #     'unsupported constructs': len(top_level_untransformed_function_like_expansions_run_1_unsupported_construct),
        #     'total': len(top_level_untransformed_function_like_expansions_run_1),
        #     'total transformed': len(top_level_function_like_transformed_expansions_run_1)
        # }

        # run_1_untransformed_top_level_stats_file = os.path.join(
        #     STATS_DIR, 'run-1-untransformed-top-level-stats.csv')

        # if not os.path.exists(run_1_untransformed_top_level_stats_file):
        #     with open(run_1_untransformed_top_level_stats_file, 'w') as ofp:
        #         print(','.join(run_1_untransformed_top_level_stats.keys()), file=ofp)

        # with open(run_1_untransformed_top_level_stats_file, 'a') as ofp:
        #     print(','.join([str(v)
        #           for v in run_1_untransformed_top_level_stats.values()]), file=ofp)

        # run_1_untransformed_top_level_olm_stats_file = os.path.join(
        #     STATS_DIR, 'run-1-untransformed-top-level-olm-stats.csv')

        # if not os.path.exists(run_1_untransformed_top_level_olm_stats_file):
        #     with open(run_1_untransformed_top_level_olm_stats_file, 'w') as ofp:
        #         print(','.join(run_1_untransformed_top_level_olm_stats.keys()), file=ofp)

        # with open(run_1_untransformed_top_level_olm_stats_file, 'a') as ofp:
        #     print(','.join([str(v)
        #           for v in run_1_untransformed_top_level_olm_stats.values()]), file=ofp)

        # run_1_untransformed_top_level_flm_stats_file = os.path.join(
        #     STATS_DIR, 'run-1-untransformed-top-level-flm-stats.csv')

        # if not os.path.exists(run_1_untransformed_top_level_flm_stats_file):
        #     with open(run_1_untransformed_top_level_flm_stats_file, 'w') as ofp:
        #         print(','.join(run_1_untransformed_top_level_flm_stats.keys()), file=ofp)

        # with open(run_1_untransformed_top_level_flm_stats_file, 'a') as ofp:
        #     print(','.join([str(v)
        #           for v in run_1_untransformed_top_level_flm_stats.values()]), file=ofp)

        with open(STATS_DIR + f'run-1-untransformed-top-level-{evaluation_program.name}.csv', 'w') as fp:
            print(
                *[field.name for field in fields(UntransformedExpansion)], sep=',', file=fp)
            for ute in all_untransformed_top_level_expansions:
                if ute.run_no_reported == 1:
                    print(*astuple(ute), sep=',', file=fp)


if __name__ == '__main__':
    main()
