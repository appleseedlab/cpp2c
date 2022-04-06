import csv
import os
import shutil
from collections import defaultdict, deque
from dataclasses import dataclass, field
from subprocess import CompletedProcess, run
from sys import stderr
from typing import Deque, Dict, List, Set
from urllib.request import urlretrieve

# TODO: Need to transform each program multiple times, keeping track of transformed expansions each time, and not counting transformed expansions in transformed definitions twice

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

    names_of_transformed_definitions: Set[str] = field(default_factory=set)
    types_of_transformed_definitions: Set[str] = field(default_factory=set)

    expansion_spelling_locations: Set[str] = field(default_factory=set)
    transformed_expansion_spelling_locations: Set[str] = field(
        default_factory=set)

    hashes_of_macros_we_have_already_recorded_transformed_expansions_of_this_macro_in: Set[str] = field(
        default_factory=set)


@dataclass
class MacroExpansion:
    macro_hash: str
    spelling_location: str


@dataclass
class TransformedDefinition:
    macro_hash: str
    transformed_type: str
    emitted_name: str


@dataclass
class TransformedExpansion:
    macro_hash: str
    spelling_location: str
    name_of_function_spelled_in: str

    macro_hashes_of_macro_definitions_this_expansion_has_been_transformed_in_to_number_of_times_it_was_transformed_in_it: Dict[str, int] = field(
        default_factory=dict)


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


def is_not_in_source_file(location: str) -> bool:
    return (
        location.startswith(BUILTIN) or
        location.startswith(SCRATCH_SPACE) or
        location.startswith(STD_HEADER_PATH)
        or location.startswith(CLANG_HEADER_PATH))


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
    all_stats_file = os.path.join(STATS_DIR, 'all-stats.csv')

    for evaluation_program in evaluation_programs:

        run_no = 1
        macro_definitions: List[MacroDefinition] = []
        macro_expansions: List[MacroExpansion] = []
        transformed_definitions: List[TransformedDefinition] = []
        transformed_expansions: List[TransformedExpansion] = []

        macro_hashes_to_macro_defs: Dict[str, MacroDefinition] = {}

        names_of_transformed_functions_to_hashes_of_original_macros: Dict[str, str] = {
        }

        names_of_functions_to_hashes_of_macros_expanded_in_them_to_spelling_locations_of_transformed_expansions_of_those_macros_in_them: Dict[str, Dict[str, Set[str]]] = \
            defaultdict(lambda: defaultdict(set))

        print(f'Run {run_no} of {evaluation_program.name}')

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
        src_dir = os.path.join(
            evaluation_program.extracted_archive_path, evaluation_program.src_dir)

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

        # Transform program files until no more transformations are made
        while True:
            emitted_a_transformation = False

            for c_file in program_c_files:
                cp: CompletedProcess = run(
                    f'../implementation/build/bin/cpp2c {c_file} -fsyntax-only -Wno-all -Xclang -plugin-arg-cpp2c -Xclang -ow', shell=True, capture_output=True, text=True)

                emitted_a_transformation_for_this_file = False

                for line in cp.stderr.splitlines():
                    if not line.startswith(CPP2C_PREFIX):
                        continue

                    # Skip the Cpp2C message prefix
                    msg = line[len(CPP2C_PREFIX):]

                    # Ignore first field since its indicates the type of message
                    constructor_fields = parse_cpp2c_message(msg)[1:]

                    if msg.startswith(MACRO_DEFINITION):
                        # We only record macro definitions we find in run 1
                        if run_no != 1:
                            continue

                        md = MacroDefinition(*constructor_fields)

                        # Ignore definitions from header files
                        if is_not_in_source_file(md.definition_location):
                            continue

                        macro_definitions.append(md)
                        macro_hashes_to_macro_defs[md.macro_hash] = md

                    elif msg.startswith(MACRO_EXPANSION):
                        # We only record macro expansions we find in run 1
                        if run_no != 1:
                            continue

                        me = MacroExpansion(*constructor_fields)

                        # Ignore expansions not in the source file,
                        # and ignore expansions of macro not defined
                        # in the source file
                        if (
                            is_not_in_source_file(me.spelling_location) or
                            # If the macro hash of this macro is not in the
                            # macro hashes map, then it must not have been
                            # defined in the program source code
                            me.macro_hash not in macro_hashes_to_macro_defs
                        ):
                            continue

                        macro_expansions.append(me)
                        macro_hashes_to_macro_defs[me.macro_hash].expansion_spelling_locations.add(
                            me.spelling_location)

                    elif msg.startswith(TRANSFORMED_DEFINITION):
                        # Accumulate transformed definitions across runs
                        td = TransformedDefinition(*constructor_fields)

                        transformed_definitions.append(td)
                        macro_hashes_to_macro_defs[td.macro_hash].names_of_transformed_definitions.add(
                            td.emitted_name)
                        macro_hashes_to_macro_defs[td.macro_hash].types_of_transformed_definitions.add(
                            td.transformed_type)

                        names_of_transformed_functions_to_hashes_of_original_macros[td.emitted_name] = \
                            td.macro_hash

                    elif msg.startswith(TRANSFORMED_EXPANSION):
                        # Accumulate these across runs, but don't count them all.
                        # See below for how we process these
                        te = TransformedExpansion(*constructor_fields)

                        transformed_expansions.append(te)

                        names_of_functions_to_hashes_of_macros_expanded_in_them_to_spelling_locations_of_transformed_expansions_of_those_macros_in_them[
                            te.name_of_function_spelled_in][te.macro_hash].add(te.spelling_location)

                        emitted_a_transformation_for_this_file = True

                    else:
                        print(
                            'Found what appeared to be a CPP2C message, but was not', file=stderr)
                        print(line)
                        exit(1)

                emitted_a_transformation = emitted_a_transformation or emitted_a_transformation_for_this_file

                if emitted_a_transformation_for_this_file:
                    print(f'Emitted at least one transformation in {c_file}')

            if not emitted_a_transformation:
                break

            for te in transformed_expansions:
                # Count the number of unique transformed expansion locations.
                # For instance, say M contains 2 nested calls to P, and
                # was transformed to MF1, MF2, and MF3 in run 1.
                # In run 2, we would find 6 expansions of P in 6 different
                # spelling locations, but we would only count P as
                # having been expanded twice since MF1, MF2, and MF3 are all
                # transformed definitions of the same original macro M.

                # If we are within a transformed function_definition...
                if te.name_of_function_spelled_in in names_of_transformed_functions_to_hashes_of_original_macros.keys():
                    # ...then we have to make sure to count the set of expansions
                    # of this macro in only one of its transformed definitions
                    hash_of_macro_this_expansion_was_spelled_in = names_of_transformed_functions_to_hashes_of_original_macros[
                        te.name_of_function_spelled_in]

                    if hash_of_macro_this_expansion_was_spelled_in not in macro_hashes_to_macro_defs[te.macro_hash].hashes_of_macros_we_have_already_recorded_transformed_expansions_of_this_macro_in:
                        macro_hashes_to_macro_defs[te.macro_hash].transformed_expansion_spelling_locations |= names_of_functions_to_hashes_of_macros_expanded_in_them_to_spelling_locations_of_transformed_expansions_of_those_macros_in_them[te.name_of_function_spelled_in][te.macro_hash]

                        macro_hashes_to_macro_defs[te.macro_hash].hashes_of_macros_we_have_already_recorded_transformed_expansions_of_this_macro_in.add(
                            hash_of_macro_this_expansion_was_spelled_in)

                # Otherwise, we unequivocally count this expansion
                else:
                    macro_hashes_to_macro_defs[te.macro_hash].transformed_expansion_spelling_locations.add(
                        te.spelling_location)

            macro_definitions_with_at_least_one_expansion = [
                md for md in macro_definitions if len(md.expansion_spelling_locations) > 0]

            macro_definitions_transformed_at_least_once = [
                # We could also use macro_definitions here
                md for md in macro_definitions_with_at_least_one_expansion
                if len(md.types_of_transformed_definitions) > 0]

            total_unique_original_expansions = sum(
                [len(md.expansion_spelling_locations) for md in macro_definitions])

            total_unique_transformed_expansions = sum(
                [len(md.transformed_expansion_spelling_locations)
                    for md in macro_definitions]
            )

            # print(transformed_expansions)

            stats = {
                # For program X...
                'program name': evaluation_program.name,

                # ...on run #N...
                'run #': run_no,

                # ...we found a total of X macro definitions...
                'macro definitions': len(macro_definitions),

                # ...of these definitions, Y were expanded at least once...
                'expanded macro definitions': len(macro_definitions_with_at_least_one_expansion),

                # ...and of these definitions, we transformed Z at least once.
                'transformed macro definitions': len(macro_definitions_transformed_at_least_once),

                # We found a total of X unique original macro expansions...
                'unique original expanions': total_unique_original_expansions,

                # ...of these expansions, we transformed Y of them
                'transformed unique expansions': total_unique_transformed_expansions,
                # 'total transformed expansions': len(transformed_expansions)
            }

            output_fn = f'{evaluation_program.name}-run-{run_no}.csv'
            with open(os.path.join(STATS_DIR, output_fn), 'w') as ofp:
                items = stats.items()
                print(','.join([item[0] for item in items]), file=ofp)
                print(','.join([str(item[1]) for item in items]), file=ofp)

            run_no += 1

            if not os.path.exists(all_stats_file):
                with open(all_stats_file, 'w') as ofp:
                    print(','.join(stats.keys()), file=ofp)

            with open(all_stats_file, 'a') as ofp:
                # NOTE: this is safe to do since iterating a dict
                # in Python is consistent
                print(','.join([str(v) for v in stats.values()]), file=ofp)


if __name__ == '__main__':
    main()
