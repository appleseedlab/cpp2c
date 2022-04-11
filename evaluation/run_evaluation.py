import csv
import os
import shutil
from collections import deque
from dataclasses import dataclass
from subprocess import CompletedProcess, run
from sys import stderr
import sys
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
def fivenum(data):
    """Five-number summary."""
    try:
        return np.percentile(data, [0, 25, 50, 75, 100], method='midpoint')
    # Happens if we pass an empty array
    except IndexError:
        return [0, 0, 0, 0, 0]


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

        # Transform program files until no more transformations are made
        while True:
            run_no += 1
            print(f'Run {run_no} of {evaluation_program.name}')
            macro_definitions_found_this_run: List[MacroDefinition] = []
            macro_expansions_found_this_run: List[MacroExpansion] = []
            transformed_definitions_found_this_run: List[TransformedDefinition] = \
                []
            transformed_expansions_found_this_run: List[TransformedExpansion] = \
                []

            emitted_a_transformation = False

            for c_file in program_c_files:

                macro_definitions_found_in_this_translation_unit: List[MacroDefinition] = \
                    []
                macro_expansions_found_in_this_translation_unit: List[MacroExpansion] = \
                    []
                transformed_definitions_found_in_this_translation_unit: List[TransformedDefinition] = \
                    []
                transformed_expansions_found_in_this_translation_unit: List[TransformedExpansion] = \
                    []

                cp: CompletedProcess = run(
                    f'../implementation/build/bin/cpp2c {c_file} -fsyntax-only -Wno-all -Xclang -plugin-arg-cpp2c -Xclang -ow',
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
                        macro_definitions_found_in_this_translation_unit.append(
                            MacroDefinition(*constructor_fields, run_no))

                    elif msg.startswith(MACRO_EXPANSION):
                        macro_expansions_found_in_this_translation_unit.append(
                            MacroExpansion(*constructor_fields, run_no))

                    elif msg.startswith(TRANSFORMED_DEFINITION):
                        transformed_definitions_found_in_this_translation_unit.append(
                            TransformedDefinition(*constructor_fields, run_no))

                    elif msg.startswith(TRANSFORMED_EXPANSION):
                        transformed_expansions_found_in_this_translation_unit.append(
                            TransformedExpansion(*constructor_fields, run_no))
                        emitted_a_transformation_for_this_file = True

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
                transformed_definitions_found_this_run.extend(
                    transformed_definitions_found_in_this_translation_unit)
                transformed_expansions_found_this_run.extend(
                    transformed_expansions_found_in_this_translation_unit)

                emitted_a_transformation = emitted_a_transformation or emitted_a_transformation_for_this_file

                # if emitted_a_transformation_for_this_file:
                #     print(f'Emitted at least one transformation in {c_file}')

            # Add what we found this run to the total
            all_macro_definitions.extend(
                macro_definitions_found_this_run)
            all_macro_expansions.extend(
                macro_expansions_found_this_run)
            all_transformed_definitions.extend(
                transformed_definitions_found_this_run)
            all_transformed_expansions.extend(
                transformed_expansions_found_this_run)

            if not emitted_a_transformation:
                break

        # Examine only the definitions that we found in the first run
        # that were defined in the evaluation program
        run_1_macro_definitions_in_evaluation_program = \
            [
                md for md in all_macro_definitions
                if (
                    md.run_no_found == 1 and
                    is_location_in_extracted_program_c_or_h_file(
                        md.definition_location)
                )
            ]

        # Collect set of all unique macro definitions in the source program
        hashes_of_run_1_macro_definitions_in_evaluation_program = \
            {md.macro_hash for md in run_1_macro_definitions_in_evaluation_program}

        # Number of unique macro definitions
        total_unique_macro_definitions = \
            len(hashes_of_run_1_macro_definitions_in_evaluation_program)

        total_unique_object_like_macro_definitions = \
            len({mh for mh in hashes_of_run_1_macro_definitions_in_evaluation_program if mh.startswith(
                OBJECT_LIKE_PREFIX)})

        total_unique_function_like_macro_definitions =\
            len({mh for mh in hashes_of_run_1_macro_definitions_in_evaluation_program if mh.startswith(
                FUNCTION_LIKE_PREFIX)})

        # Collect the set of expansions of macros defined in the source program
        run_1_expansions_of_macros_defined_in_evaluation_program = \
            [
                me for me in all_macro_expansions
                if (
                    me.run_no_found == 1 and
                    me.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program
                )
            ]

        # Collect all unique macro expansion locations
        unique_original_expansion_spelling_locations = \
            {
                me.spelling_location
                for me in run_1_expansions_of_macros_defined_in_evaluation_program
            }
        # Count the number of unique original macro expansions
        # This includes, but does not duplicate, spelling locations
        # of nested macro expansions
        total_unique_original_expansions = \
            len(unique_original_expansion_spelling_locations)
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

        # Map each original macro definition in the evaluation program
        # to the set of unique spelling locations it was expanded at
        hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations = {
            mh: set() for mh in hashes_of_run_1_macro_definitions_in_evaluation_program
        }
        for me in run_1_expansions_of_macros_defined_in_evaluation_program:
            hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations[me.macro_hash].add(
                me.spelling_location)
        five_point_summary_of_unique_invocations_per_definition = fivenum(
            [len(unique_invocations)
             for unique_invocations in hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations.values()]
        )
        five_point_summary_of_unique_object_like_invocations_per_definition = fivenum(
            [
                len(unique_invocations)
                for mh, unique_invocations in hashes_of_run_1_macro_definitions_in_evaluation_program_to_unique_invocations.items()
                if mh.startswith(OBJECT_LIKE_PREFIX)
            ]
        )
        five_point_summary_of_unique_function_like_invocations_per_definition = fivenum(
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
                names_of_functions_to_check_for_transformed_expansions_in.add(te.name_of_function_spelled_in)
        
        unique_transformed_expansions = []
        for i in range(1, run_no):
            # Add all expansions to our list of unique expansions which were found
            # in one of the function definitions that we confirmed were good to check in
            unique_transformations_found_this_round = []
            for te in all_expansions_of_macros_defined_in_evaluation_program:
                if te.run_no_emitted == i:
                    if te.name_of_function_spelled_in in names_of_functions_to_check_for_transformed_expansions_in:
                        unique_transformations_found_this_round.append(te)
            
            unique_transformed_expansions.extend(unique_transformations_found_this_round)

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
                    hashes_of_macros_to_no_longer_check_for_transformed_expansions_in.add(f.macro_hash)

            # Add the names of these new functions to the names of the
            # functions to check for new transformed expansions in
            names_of_new_functions_to_check_for_transformed_expansions_in = \
                {f.emitted_name for f in unique_functions_emitted_this_run}
            names_of_functions_to_check_for_transformed_expansions_in.update(names_of_new_functions_to_check_for_transformed_expansions_in)
            

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

        distribution_of_unique_function_signatures_per_transformed_definition = fivenum(
            [
                len(sigs) for sigs in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.values()
                if len(sigs) > 0
            ]
        )
        distribution_of_unique_function_signatures_per_transformed_object_like_definition = fivenum(
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
        distribution_of_unique_function_signatures_per_transformed_function_like_definition = fivenum(
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

        five_point_summary_of_transformed_invocations_per_transformed_defintion = fivenum(
            [
                len(unique_transformations) for unique_transformations in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program.values()
            ])
        five_point_summary_of_transformed_object_like_invocations_per_transformed_defintion = fivenum(
            [
                len(unique_transformations)
                for mh, unique_transformations in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_unique_transformed_expansions_in_evaluation_program.items()
                if mh.startswith(OBJECT_LIKE_PREFIX)
            ])
        five_point_summary_of_transformed_function_like_invocations_per_transformed_defintion = fivenum(
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

        five_point_summary_of_not_transformed_invocations_per_transformed_defintion = fivenum(
            list(hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.values())
        )

        five_point_summary_of_not_transformed_object_like_invocations_per_transformed_defintion = fivenum(
            [
                num_not_transformed
                for mh, num_not_transformed in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.items()
                if mh.startswith(OBJECT_LIKE_PREFIX)
            ])

        five_point_summary_of_not_transformed_function_like_invocations_per_transformed_defintion = fivenum(
            [
                num_not_transformed
                for mh, num_not_transformed in
                hashes_of_run_1_macro_definitions_in_evaluation_program_transformed_at_least_once_to_run_1_num_expansions_not_transformed.items()
                if mh.startswith(FUNCTION_LIKE_PREFIX)
            ])

        # TODO: How can we use the prefix to only check one type of macro?
        # We can't just ignore hashes of the other type, because an
        # object-like macro may be expanded inside a function-like macro,
        # and we'd need to record the name of that FLM to check its
        # transformed definition when looking for newly emitted
        # unique transformations in subsequent runs

        all_stats = {
            'program name': evaluation_program.name,
            '# of runs': run_no,
            'total unique definitions': total_unique_macro_definitions,
            'unique transformed definitions': num_run_1_macro_definitions_transformed_at_least_once,
            'total unique invocations': total_unique_original_expansions,
            'unique transformed invocations': num_unique_transformed_expansions,
            'unique not transformed invocations': total_unique_original_expansions - num_unique_transformed_expansions,
            'distribution of unique invocations per definition': five_point_summary_of_unique_invocations_per_definition,
            'distribution of not transformed invocations per transformed definition': five_point_summary_of_not_transformed_invocations_per_transformed_defintion,
            'distribution of transformed invocations per transformed definition': five_point_summary_of_transformed_invocations_per_transformed_defintion,
            'distribution of unique function signatures per transformed definition': distribution_of_unique_function_signatures_per_transformed_definition
        }

        olm_stats = {
            'program name': evaluation_program.name,
            '# of runs': run_no,
            'total unique definitions': total_unique_object_like_macro_definitions,
            'unique transformed definitions': num_run_1_object_like_macro_definitions_transformed_at_least_once,
            'total unique invocations': total_unique_original_object_like_expansions,
            'unique transformed invocations': num_unique_object_like_transformed_expansions,
            'unique not transformed invocations': total_unique_original_object_like_expansions - num_unique_object_like_transformed_expansions,
            'distribution of unique invocations per definition': five_point_summary_of_unique_object_like_invocations_per_definition,
            'distribution of not transformed invocations per transformed definition': five_point_summary_of_not_transformed_object_like_invocations_per_transformed_defintion,
            'distribution of transformed invocations per transformed definition': five_point_summary_of_transformed_object_like_invocations_per_transformed_defintion,
            'distribution of unique function signatures per transformed definition': distribution_of_unique_function_signatures_per_transformed_object_like_definition
        }

        flm_stats = {
            'program name': evaluation_program.name,
            '# of runs': run_no,
            'total unique definitions': total_unique_function_like_macro_definitions,
            'unique transformed definitions': num_run_1_function_like_macro_definitions_transformed_at_least_once,
            'total unique invocations': total_unique_original_function_like_expansions,
            'unique transformed invocations': num_unique_function_like_transformed_expansions,
            'unique not transformed invocations': total_unique_original_function_like_expansions - num_unique_function_like_transformed_expansions,
            'distribution of unique invocations per definition': five_point_summary_of_unique_function_like_invocations_per_definition,
            'distribution of not transformed invocations per transformed definition': five_point_summary_of_not_transformed_function_like_invocations_per_transformed_defintion,
            'distribution of transformed invocations per transformed definition': five_point_summary_of_transformed_function_like_invocations_per_transformed_defintion,
            'distribution of unique function signatures per transformed definition': distribution_of_unique_function_signatures_per_transformed_function_like_definition
        }

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

    # TODO: Add flag to run these programs' tests
    # W have hand-confirmed that they all work after the current
    # implementation transforms them, but it would greatly facilitate future
    # testing


if __name__ == '__main__':
    main()
