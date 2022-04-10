import csv
import os
import shutil
from collections import deque
from dataclasses import dataclass
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

BUILTIN = r'<built-in>'
SCRATCH_SPACE = r'<scratch space>'
STD_HEADER_PATH = r'/usr/include'
CLANG_HEADER_PATH = r'/usr/lib'
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
    return np.percentile(data, [0, 25, 50, 75, 100], method='midpoint')


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
        EvaluationProgram(
            r'test',
            r'test.zip',
            r'.',
            r''
        )
    ]

    shutil.rmtree(STATS_DIR, ignore_errors=True)
    os.makedirs(STATS_DIR, exist_ok=True)
    all_stats_file = os.path.join(STATS_DIR, 'all-stats.csv')

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

        all_expansions_of_macros_defined_in_evaluation_program = \
            [
                te for te in all_transformed_expansions
                if te.macro_hash in hashes_of_run_1_macro_definitions_in_evaluation_program
            ]

        # Count all transformations of expansions we found in run 1,
        # because we can be sure that these are all unique transformations
        unique_transformed_expansions: List[TransformedExpansion] = []
        for te in all_expansions_of_macros_defined_in_evaluation_program:
            if te.run_no_emitted == 1:
                unique_transformed_expansions.append(te)

        # For a subsequent run, we only count transformations of expansions
        # inside function definitions that we emitted in the previous run,
        # excluding both duplicate polymorphic definitions and definitions
        # we checked in prior runs
        # This is complicated by the fact that we may have emitted multiple
        # identical definitions for a macro that we transformed an expansion
        # of in a prior run to make them polymorphic
        hashes_of_macros_to_no_longer_check_for_transformed_expansions_in = set()
        for i in range(2, run_no):
            # print('Counting unique expansions in round', i)
            names_of_functions_emitted_in_previous_round = \
                {
                    td.emitted_name for td in all_transformed_definitions
                    if td.run_no_emitted == i-1
                }
            names_of_new_functions_we_emitted_in_previous_round_for_a_single_type = set()
            macro_hashes_mapped_to_whether_weve_seen_a_definition_for_them_yet = {}

            def have_we_already_seen_a_transformed_definition_for_this_macro(mh: str) -> bool:
                return (
                    macro_hashes_mapped_to_whether_weve_seen_a_definition_for_them_yet.get(mh, False) or
                    mh in hashes_of_macros_to_no_longer_check_for_transformed_expansions_in
                )

            def record_that_weve_seen_a_transformed_definition_for_this_macro(mh: str) -> None:
                macro_hashes_mapped_to_whether_weve_seen_a_definition_for_them_yet[mh] = True

            for td in all_transformed_definitions:
                if td.emitted_name in names_of_functions_emitted_in_previous_round:
                    if not have_we_already_seen_a_transformed_definition_for_this_macro(td.macro_hash):
                        record_that_weve_seen_a_transformed_definition_for_this_macro(
                            td.macro_hash)
                        names_of_new_functions_we_emitted_in_previous_round_for_a_single_type.add(
                            td.emitted_name)

            unique_transformations_found_this_round = []
            for te in all_expansions_of_macros_defined_in_evaluation_program:
                if te.run_no_emitted == i:
                    if te.name_of_function_spelled_in in names_of_new_functions_we_emitted_in_previous_round_for_a_single_type:
                        unique_transformations_found_this_round.append(te)

            hashes_of_macros_to_no_longer_check_for_transformed_expansions_in.update(
                macro_hashes_mapped_to_whether_weve_seen_a_definition_for_them_yet.keys())

            unique_transformed_expansions.extend(
                unique_transformations_found_this_round)

        num_unique_transformed_expansions = len(unique_transformed_expansions)

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

        distribution_of_unique_function_signatures_per_transformed_definition = fivenum(
            [
                len(sigs) for sigs in hashes_of_run_1_macro_definitions_in_evaluation_program_to_signatures_of_transformed_definitions.values()
                if len(sigs) > 0
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

        stats = {
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

        output_fn = f'{evaluation_program.name}-run-{run_no}.csv'
        with open(os.path.join(STATS_DIR, output_fn), 'w') as ofp:
            items = stats.items()
            print(','.join([item[0] for item in items]), file=ofp)
            print(','.join([str(item[1]) for item in items]), file=ofp)

        if not os.path.exists(all_stats_file):
            with open(all_stats_file, 'w') as ofp:
                print(','.join(stats.keys()), file=ofp)

        with open(all_stats_file, 'a') as ofp:
            # NOTE: this is safe to do since iterating a dict
            # in Python is consistent
            print(','.join([str(v) for v in stats.values()]), file=ofp)

    # TODO: Add flag to run these programs' tests
    # W have hand-confirmed that they all work after the current
    # implementation transforms them, but it would greatly facilitate future
    # testing


if __name__ == '__main__':
    main()
