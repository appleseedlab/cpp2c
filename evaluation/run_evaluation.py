import json
import os
import shutil
import subprocess
import sys
from collections import defaultdict
from datetime import datetime
from operator import itemgetter
from typing import Any, DefaultDict, Dict, List, Set, Sized
from urllib.request import urlretrieve
import clang.cindex
import numpy as np

import abstractometer
import compile_command
import summaries
from evaluation_programs import EVALUATION_PROGRAMS

MACRO_DEFINITION_PREFIX = 'CPP2C:Macro Definition'
RAW_MACRO_EXPANSION_PREFIX = 'CPP2C:Raw Macro Expansion'
POTENTIALLY_TRANSFORMABLE_MACRO_EXPANSION_PREFIX = 'CPP2C:Potentially Transformable Macro Expansion'
TRANSFORMED_DEFINITION_PREFIX = 'CPP2C:Transformed Definition'
TRANSFORMED_EXPANSION_PREFIX = 'CPP2C:Transformed Expansion'
UNTRANSFORMED_EXPANSION_PREFIX = 'CPP2C:Untransformed Expansion'

OLM_TAG = 'object-like'
FLM_TAG = 'function-like'

CATEGORIES_NOT_TRANSFORMED = [
    'Syntactic well-formedness',
    'Environment capture',
    'Parameter side-effects',
    'Unsupported construct',
    'Turned off construct'
]


def is_system_header_path(path: str) -> bool:
    '''
    Returns true if this path is:
    - Blank
    - A system header path
    - Scratch space (still not sure what this is)
    '''
    return any((path == '',
                '/usr/include' in path,
                '/usr/lib' in path,
                '<scratch space>' in path))


def mhash_dict_len_stat(stat: str, d: Dict[str, Any]):
    print(f'{stat}: {len(d)}')
    print(f'    olms: {len([h for h in d if OLM_TAG in h])}')
    print(f'    flms: {len([h for h in d if FLM_TAG in h])}')


def mhash_dict_sum_values_lens_stat(stat: str, d: Dict[str, Sized]):
    print(f'{stat}: {sum([len(vs) for _, vs in d.items()])}')
    print(f'    olms: {sum([len(vs) for h, vs in d.items() if OLM_TAG in h])}')
    print(f'    flms: {sum([len(vs) for h, vs in d.items() if FLM_TAG in h])}')


def mhash_dict_sum_values_stat(stat: str, d: Dict[str, int]):
    print(f'{stat}: {sum([v for _, v in d.items()])}')
    print(f'    olms: {sum([v for h, v in d.items() if OLM_TAG in h])}')
    print(f'    flms: {sum([v for h, v in d.items() if FLM_TAG in h])}')


def mhash_set_len_stat(stat: str, s: Set[str]):
    print(f'{stat}: {len(s)}')
    print(f'    olms: {len([h for h in s if OLM_TAG in h])}')
    print(f'    flms: {len([h for h in s if FLM_TAG in h])}')


def num_stat(stat: str, i: int):
    print(f'{stat}: {i}')


def str_stat(stat: str, s: str):
    print(f'{stat}: {s}')


def top_five_macros_by_val_len(d: Dict[str, Sized]):
    return sorted(
        [
            (mhash.split(';')[0],  # macro name
             len(vs))  # number of values
            for mhash, vs in d.items()
        ],
        key=itemgetter(1),  # number of values
        reverse=True  # sort in descending order
    )[:5]  # select the top five


def top_five_macros_by_val(d: Dict[str, int]):
    return sorted(
        [
            (mhash.split(';')[0],  # macro name
             v)  # value
            for mhash, v in d.items()
        ],
        key=itemgetter(1),  # value
        reverse=True  # sort in descending order
    )[:5]  # select the top five


def main():

    # Whether to transform macros relying on conditional evaluation
    tce = len(sys.argv) == 2 and sys.argv[1] == 'tce'
    results_dir = r'results-tce/' if tce else r'results/'

    # Get the full path to the cpp2c shared object file
    cpp2c_so_path = r'../implementation/build/lib/libCpp2C.so'
    if os.path.exists(cpp2c_so_path):
        cpp2c_so_path = os.path.realpath(cpp2c_so_path)
    else:
        print("error: cpp2c.so not found", file=sys.stderr)
        return 1

    # Create the results dir if it does not exist
    os.makedirs(results_dir, exist_ok=True)

    # Disable numpy text wrapping
    np.set_printoptions(linewidth=np.inf)

    for evaluation_program in EVALUATION_PROGRAMS:

        # Change std out to outfile
        # FIXME: This is messy, should be using context managers instead
        ofp_fn = os.path.join(results_dir, evaluation_program.name + '.txt')
        ofp = open(ofp_fn, 'w')
        sys.stdout = ofp

        # Download the program zip file if we do not already have it
        if not os.path.exists(evaluation_program.archive_file):
            print(f'Downloading {evaluation_program.name} from {evaluation_program.link_to_archive_file}', file=sys.stderr)

            # Download the program's archive
            if evaluation_program.link_to_archive_file.startswith('http'):
                # http(s) download
                urlretrieve(evaluation_program.link_to_archive_file, evaluation_program.archive_file)
            elif evaluation_program.link_to_archive_file.startswith('ftp'):
                # ftp download
                # TODO: Use ftp lib instead of relying on wget
                subprocess.run(f'wget --no-passive {evaluation_program.link_to_archive_file}', shell=True)

            print(f'Finished downloading {evaluation_program.name}', file=sys.stderr)

        # Delete the old extracted archive
        shutil.rmtree(evaluation_program.extracted_archive_path, ignore_errors=True)

        # Create a fresh extracted archive
        shutil.unpack_archive(evaluation_program.archive_file, evaluation_program.extract_dir)

        # Save the current directory so we can move back to it after
        # evaluating this program
        evaluation_dir = os.getcwd()

        print(f'{evaluation_program.name}')

        # Configure program and generate compile_commands.json
        print(f'Building {evaluation_program.name}', file=sys.stderr)
        os.chdir(evaluation_program.extracted_archive_path)
        build_start_time = datetime.now()
        subprocess.run(evaluation_program.configure_compile_commands_script, shell=True, capture_output=True)
        build_end_time = datetime.now()
        print(f'Finished building {evaluation_program.name}', file=sys.stderr)
        build_elapsed_time = build_end_time - build_start_time
        str_stat('time to build', f'{build_elapsed_time.seconds}s {build_elapsed_time.microseconds}us')

        # Collect compile commands from compile_commands.json
        compile_commands = compile_command.load_compile_commands_from_file('compile_commands.json')
        # Only transform .c and .h files that were compiled with a C compiler.
        # We can't transform files compiled with a C++ compiler because
        # C++ handles global static variable slightly differently than
        # C does.
        # For instance, consider the following three files:
        # header.h          |   a.c                 |   b.c
        # static int X;         #include "header.h"     #include "header.h"
        #                       static int X = 0;       static int X = 0;
        # if we run `gcc a.c b.c`, the code will compile.
        # however, if we run `g++ a.c b.c`, it will fail to compile with
        # a redefinition error.
        # we use the static keyword to easily transform entire c programs.
        # we could do a more sophisticated approach using the extern keyword
        # in header files instead, and this would work with c++, but this
        # would require build system analysis, which i don't feel ready
        # to tackle yet.
        # so for now, we only transformed .c and .h files that are compiled
        # by a c compiler.
        compile_commands = [ cc for cc in compile_commands
                             if (cc.file.endswith('.c') or
                                cc.file.endswith('.h')) and
                                ('++' not in cc.arguments[0]) ]

        # Loop 1: Pre-transformation abstraction factor
        # TODO: Put this into a function so we don't have to repeat this
        #       code at the end.

        expr_depths: List[int] = []
        func_var_names: Set[str] = set()
        unique_syms: Dict[str, Set[str]] = {}
        for cc in compile_commands:
            os.chdir(cc.directory)
            # remove the first and last arguments since they are the compiler
            # name and the name of the file, and then fix the remaining
            # arguments
            args = compile_command.fix_args_for_clang(cc.arguments[1:-1])
            idx = clang.cindex.Index.create()
            tu: clang.cindex.TranslationUnit = idx.parse(cc.file, args)
            c: clang.cindex.Cursor = tu.cursor
            expr_depths += abstractometer.get_expr_depths(c)
            func_var_names |= abstractometer.get_func_var_names(c)
            unique_syms.update(abstractometer.get_unique_decls_refd_in_function_definitions(c))
            # TODO: test this and check that it actually works

        print('avg expr nesting depth after:', (sum(expr_depths) / len(expr_depths)) if len(expr_depths) > 0 else 0)
        print('num function and global names:', len(func_var_names))
        print('avg unique symbols per function:',
          (sum([len(us) for us in unique_syms])
           / len(unique_syms))
          if len(unique_syms) > 0 else 0)

        # Loop 2: Macro metrics
        # - Count the number of unique macro definitions that are
        #   defined in the source program itself.
        # - Count the number of unique invocations in the source program
        #   of macros defined in the source program.
        #   + Two invocations are unique if they have different
        #     spelling locations.
        # - We accomplish these goals by performing a dry run in which
        #   we don't make any changes to the program and instead just count
        #   the number of unique source definitions and invocations found.

        print(f'Counting unique macro defs+invks in {evaluation_program.name}', file=sys.stderr)

        source_macro_definitions: Set[str] = set()
        mhash_to_raw_expansion_spelling_locations: DefaultDict[str, set(str)] = defaultdict(set)
        for cc in compile_commands:
            opts = ['tr', '-v'] + (['-tce'] if tce else [])
            cmd = compile_command.cpp2c_command_from_compile_command(cpp2c_so_path, cc, opts)
            os.chdir(cc.directory)
            cp = subprocess.run(cmd, shell=True, capture_output=True, text=True, errors='ignore')

            for line in cp.stderr.splitlines():

                # Check if Clang crashed
                if 'PLEASE' in line:
                    print(cp.stderr)
                    return

                elif line.startswith(MACRO_DEFINITION_PREFIX):
                    _, mhash, sloc = line.split('\t')
                    mname, mtype, mdefpath, mnum = mhash.split(';')
                    # Only record expansions of macros defined in the source program
                    if not is_system_header_path(mdefpath):
                        source_macro_definitions.add(mhash)

                elif line.startswith(RAW_MACRO_EXPANSION_PREFIX):
                    _, mhash, sloc = line.split('\t')
                    mname, mtype, mdefpath, mnum = mhash.split(';')
                    # Only record expansions of macros defined in the source program
                    if not is_system_header_path(mdefpath):
                        mhash_to_raw_expansion_spelling_locations[mhash].add(sloc)

        print(f'Finished counting unique macro defs+invks in {evaluation_program.name}', file=sys.stderr)

        mhash_dict_len_stat(f'source macro definitions', source_macro_definitions)
        mhash_dict_len_stat(f'expanded source macro definitions', mhash_to_raw_expansion_spelling_locations)

        # Compute the number of unique raw invocations this way because
        # (I think) two invocations can have the same spelling location
        # (e.g. for nested macros which begin with a nested invocation)
        unique_raw_source_macro_expansions = sum([
            len(vs) for _, vs in
            mhash_to_raw_expansion_spelling_locations.items()])
        num_stat('unique source macro expansions', unique_raw_source_macro_expansions)

        # Loop 3: Macro transformation metrics
        # - Measure time needed to transform program to a fixed point.
        # - Measure max time needed to transform each file across all runs.
        # - Count runs needed to transform program to a fixed point.
        # - Count potentially transformable definitions.
        #   + If a macro has a potentially transformable expansion,
        #     then it is a potentially transformable definition.
        # - Count potentially transformable invocations.
        #   + If a unique invocation is of a potentially transformable
        #     definition, then it is a potentially transformable invocation
        #   + NOTE:
        #     I don't think we can expose new expansions by transforming.
        #     By new, I mean expansions of macros that were not expanded
        #     in the original program; more expansions of macros that
        #     were in the original program (e.g., by transforming macros
        #     with nested invocations) is fine.
        #     * If we can't, we should create this set by including all
        #       original invocations of potentially transformable macros.
        #     * If we can, then I'm not sure how to correctly count this.
        # - Count transformed macro definitions.
        #   + Definitions with at least one transformed invocation.
        # - Count untransformed macro definitions.
        #   + Definitions with no transformed invocations.
        # - Hardest one: Unique transformed invocations.
        #   + The following assumes deduplication during transformation is
        #     correct, which so far it seems to be.
        #   + Each transformed macro will have one transformed declaration
        #     for each of its uniquely typed transformations.
        #   + Each macro+signature combination will have at most one
        #     transformed definition in each source file.
        #     Visually:
        #
        #                        definition
        #                       /
        #            declaration
        #           /           \
        #          /             definition
        #     macro
        #          \             definition
        #           \           /
        #            declaration
        #                       \
        #                        definition
        #
        #   + Naively, we could count the number of transformed invocations
        #     by jut counting the transformed invocation messages
        #     that Cpp2C emits.
        #     The problem with this is that a macro may contain
        #     nested invocations, and one macro may have multiple definitions,
        #     so if we just count all invocations as unique,
        #     we could have duplicates.
        #   + To fix this, we need to only count transformed invocations that
        #     appear in either:
        #     a) Source program function definitions.
        #     b) The first encountered transformed definition of a macro.
        #   + We will need a way to identify transformed invocations.
        #   + Idea
        #     * For each file
        #       -- For each function definition found in this file
        #             ++ If this definition is a source definition,
        #                then count all invocations found in it.
        #                Otherwise, only count its invocations if the definition
        #                is a transformed definition of a macro who we have not
        #                encountered a transformed definition for yet, *and*
        #                we have not seen this definition before
        #                in another file.
        #     * Note: with this approach, the run number in which invocations
        #       were found is irrelevant.
        # - Count untransformed macro invocations.
        #   + Maybe we could count this by looking at the untransformed
        #     invocation messages that Cpp2C emits, but because
        #         Potentially transformable invocations
        #       - Transformed invocations
        # - Categorize macros by reason(s) they were not transformed.
        #   + One category for each property and an extra category
        #     if a macro was not transformed for multiple reasons.
        # - Count number of polymorphic macro *definitions*.
        #   + Macros whose set of expansion signatures has a cardinality > 1.
        # - Count number of polymorphic macro *transformations*.
        #   + Macros whose set of transformed signatures has a cardinality > 1.

        runs_to_fixed_point = 0
        program_transform_start_time = datetime.now()

        potentially_transformable_macros: Set[str] = set()
        potentially_transformable_macros_to_raw_sigs: DefaultDict[str, Set[str]] = defaultdict(set)

        file_realpath_to_max_time_needed_to_transform: Dict[str, datetime.timedelta] = {}
        file_realpath_to_sum_time_needed_to_transform: Dict[str, datetime.timedelta] = {}

        mhash_to_cats_not_transformed: DefaultDict[str, Set[str]] = defaultdict(set)

        transformed_decl_names: Set[str] = set()
        transformed_macros: Set[str] = set()
        mhash_to_transformed_def_to_visit: Dict[str, str] = {}
        fp_to_fdecl_to_unique_invocation_mhashes: DefaultDict[str, DefaultDict[str, List[str]]] = \
            defaultdict(lambda: defaultdict(list))

        mhash_to_transformed_types: DefaultDict[str, Set[str]] = defaultdict(set)

        macros_transformed_to_vars: Set[str] = set()

        print(f'Transforming {evaluation_program.name}', file=sys.stderr)

        while True:
            emitted_a_transformation = False
            for cc in compile_commands:
                opts = ['tr', '-dd', '-i', '-v'] + (['-tce'] if tce else [])
                cmd = compile_command.cpp2c_command_from_compile_command(cpp2c_so_path, cc, opts)
                # Change to the command directory to run the command
                os.chdir(cc.directory)
                file_transform_start_time = datetime.now()
                cp = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                file_transform_end_time = datetime.now()
                file_transform_elapsed_time = file_transform_end_time - file_transform_start_time
                file_realpath = os.path.join(cc.directory+'/', cc.file)
                if ((file_realpath not in file_realpath_to_max_time_needed_to_transform) or
                    (file_realpath_to_max_time_needed_to_transform[file_realpath] < file_transform_elapsed_time)):
                    file_realpath_to_max_time_needed_to_transform[file_realpath] = file_transform_elapsed_time
                if file_realpath not in file_realpath_to_sum_time_needed_to_transform:
                    file_realpath_to_sum_time_needed_to_transform[file_realpath] = file_transform_elapsed_time
                else:
                    file_realpath_to_sum_time_needed_to_transform[file_realpath] += file_transform_elapsed_time
                for line in cp.stderr.splitlines():

                    # Check if Clang crashed
                    if 'PLEASE' in line:
                        print(cp.stderr)
                        return

                    elif line.startswith(POTENTIALLY_TRANSFORMABLE_MACRO_EXPANSION_PREFIX):
                        _, mhash, raw_sig = line.split('\t')
                        potentially_transformable_macros.add(mhash)
                        potentially_transformable_macros_to_raw_sigs[mhash].add(raw_sig)

                    elif line.startswith(TRANSFORMED_EXPANSION_PREFIX):
                        #  Record that we transformed an expansion this run
                        emitted_a_transformation = True
                        _, mhash, transformed_name, containing_function_name, ty, ast_ty = line.split('\t')

                        # If we haven't seen a transformed definition for this macro before,
                        # then mark the transformed definition this transformed expansion
                        # references as the one to visit for this macro
                        if mhash not in mhash_to_transformed_def_to_visit:
                            mhash_to_transformed_def_to_visit[mhash] = transformed_name

                        # Record that we transformed this macro
                        transformed_macros.add(mhash)

                        # Add this type to the set of transformed types for this macro
                        mhash_to_transformed_types[mhash].add(ty)

                        # Record this transformed decl name
                        transformed_decl_names.add(transformed_name)

                        # Append this macro hash to the list of hashes of transformed expansions found in
                        # this definition of this function in this file
                        fp_to_fdecl_to_unique_invocation_mhashes[file_realpath][containing_function_name] += [mhash]

                        # Count the number of macro definitions transformed to variables
                        macros_transformed_to_vars |= {mhash} if ast_ty == "var" else set()

                    elif line.startswith(UNTRANSFORMED_EXPANSION_PREFIX):
                        _, mhash, category, reason = line.split('\t')
                        mhash_to_cats_not_transformed[mhash].add(category)

            runs_to_fixed_point += 1
            print(f'finished run {runs_to_fixed_point} of {evaluation_program.name}', file=sys.stderr)
            if not emitted_a_transformation:
                break

        program_transform_end_time = datetime.now()
        program_transform_elapsed_time = program_transform_end_time - program_transform_start_time

        print(f'Finished transforming {evaluation_program.name}', file=sys.stderr)

        # Only consider potentially transformable macros which were
        # never transformed
        pt_mhash_to_cats_not_transformed = {
            mhash: cats for mhash, cats in
            mhash_to_cats_not_transformed.items()
            if mhash in potentially_transformable_macros and mhash not in transformed_macros
        }

        # Only consider expansions of macros Cpp2C said
        # it could potentially transform
        mhash_to_potentially_transformable_expansions: Dict[str, set] = {
            mhash: vs for mhash, vs in
            mhash_to_raw_expansion_spelling_locations.items()
            if mhash in potentially_transformable_macros
        }

        str_stat('time to reach a fixed point', f'{program_transform_elapsed_time.seconds}s {program_transform_elapsed_time.microseconds}us')
        num_stat('runs to reach a fixed point', runs_to_fixed_point)
        print('max time needed to transform each file')
        print(json.dumps([
            (file_realpath, f'{max_elapsed.seconds}s {max_elapsed.microseconds}us')
            for file_realpath, max_elapsed
            in file_realpath_to_max_time_needed_to_transform.items()
        ]))
        print('sum time needed to transform each file')
        print(json.dumps([
            (file_realpath, f'{max_elapsed.seconds}s {max_elapsed.microseconds}us')
            for file_realpath, max_elapsed
            in file_realpath_to_sum_time_needed_to_transform.items()
        ]))

        mhash_set_len_stat('potentially transformable macro definitions', potentially_transformable_macros)
        mhash_set_len_stat('transformed macro definitions', transformed_macros)
        mhash_dict_len_stat('untransformed potentially transformable macro definitions',
                            pt_mhash_to_cats_not_transformed)

        num_stat("number of macros transformed to vars", len(macros_transformed_to_vars))
        str_stat("percentage increase in transformed macros with our approach",
                 (str(
                     ((
                         len(transformed_macros)
                         - len(macros_transformed_to_vars))
                      / len(macros_transformed_to_vars))
                     * 100)
                  + '%')
                 if len(macros_transformed_to_vars) > 0 else 'N/A')

        # For each category, check if the set of categories of reasons
        # a macro was not transformed is a singleton list containing
        # only that category.
        # Also count macros that were not transformed for multiple categories.
        print('categories of reasons not transformed:')
        multiple_cats_count = 0
        for i, cat in enumerate(CATEGORIES_NOT_TRANSFORMED):
            count = 0
            for cats in pt_mhash_to_cats_not_transformed.values():
                if cats == {cat}:
                    count += 1

                # Only check for multiple cats on the first pass
                elif i == 0 and len(cats) > 1:
                    multiple_cats_count += 1

            print(f'    {cat.lower()}: {count}')
        print(f'    multiple categories: {multiple_cats_count}')

        print('categories of reasons not transformed (flms):')
        multiple_cats_count = 0
        for i, cat in enumerate(CATEGORIES_NOT_TRANSFORMED):
            count = 0
            for mh, cats in pt_mhash_to_cats_not_transformed.items():
                if FLM_TAG in mh:
                    if cats == {cat}:
                        count += 1

                    # Only check for multiple cats on the first pass
                    elif i == 0 and len(cats) > 1:
                        multiple_cats_count += 1

            print(f'    {cat.lower()}: {count}')
        print(f'    multiple categories: {multiple_cats_count}')

        mhash_dict_sum_values_lens_stat(f'potentially transformable invocations',
                                        mhash_to_potentially_transformable_expansions)

        mhash_to_unique_transformed_invocations: DefaultDict[str, int] = defaultdict(int)
        # Count the number of transformed invocations in source func definitions
        unique_source_transformed_invocations = 0
        for frealpath, fdecl_to_unique_invocation_mhashes in fp_to_fdecl_to_unique_invocation_mhashes.items():
            for fdecl, mhashes in fdecl_to_unique_invocation_mhashes.items():
                if fdecl not in transformed_decl_names:
                    unique_source_transformed_invocations += len(mhashes)
                    for mhash in mhashes:
                        mhash_to_unique_transformed_invocations[mhash] += 1

        num_stat('unique transformed invocations in source definitions', unique_source_transformed_invocations)

        # Count the number of transformed invocations in transformed definitions.
        # We only consider one file's definition of each canonical def
        canonical_defs = set(mhash_to_transformed_def_to_visit.values())
        canonical_defs_already_found_a_def_for: Set[str] = set()
        unique_transformed_def_transformed_invocations = 0

        # Just for fun: Keep track of which macros had the most transformed immediately nested invocations
        # canon_def_to_no_nested_invocations = defaultdict(int)

        for frealpath, fdecl_to_unique_invocation_mhashes in fp_to_fdecl_to_unique_invocation_mhashes.items():
            for fdecl, mhashes in fdecl_to_unique_invocation_mhashes.items():
                if fdecl in transformed_decl_names and fdecl in canonical_defs:
                    if fdecl not in canonical_defs_already_found_a_def_for:
                        unique_transformed_def_transformed_invocations += len(mhashes)
                        canonical_defs_already_found_a_def_for.add(fdecl)
                        # canon_def_to_no_nested_invocations[fdecl] += len(mhashes)
                        for mhash in mhashes:
                            mhash_to_unique_transformed_invocations[mhash] += 1

        num_stat('unique transformed invocations in transformed definitions',
                 unique_transformed_def_transformed_invocations)

        total_transformed_invocations = (unique_source_transformed_invocations +
                                         unique_transformed_def_transformed_invocations)

        # num_stat('total unique transformed invocations', total_transformed_invocations)
        mhash_dict_sum_values_stat('total unique transformed invocations', mhash_to_unique_transformed_invocations)

        # Which macros had the most transformed invocations?
        top_five_most_transformed_macros = top_five_macros_by_val(mhash_to_unique_transformed_invocations)
        print(f'top five most transformed macros: {top_five_most_transformed_macros}')

        potentially_transformable_invocations = sum([
            len(vs) for _, vs in
            mhash_to_potentially_transformable_expansions.items()
        ])
        untransformed_potentially_transformable_invocations = (potentially_transformable_invocations -
                                                               total_transformed_invocations)
        print(
            f'untransformed invocations: {untransformed_potentially_transformable_invocations}')

        potentially_transformable_poly_macros = {
            mhash for mhash, tys in
            potentially_transformable_macros_to_raw_sigs.items()
            if len(tys) > 1
        }

        mhash_set_len_stat('potentially transformable polymorphic macros', potentially_transformable_poly_macros)

        transformed_poly_macros = {
            mhash for mhash, tys in
            mhash_to_transformed_types.items()
            if len(tys) > 1
        }

        mhash_set_len_stat('transformed polymorphic macros', transformed_poly_macros)

        transformed_tys_twenty_num = summaries.twenty_num([len(tys) for (tys) in mhash_to_transformed_types.values()])

        print(f'twenty pt summary of transformed types: {transformed_tys_twenty_num}')

        # For fun: Which macros had the most uniquely typed transformations?
        top_five_poly_macros = top_five_macros_by_val_len(mhash_to_transformed_types)
        print(f'macros with most transformed types: {top_five_poly_macros}')

        # Loop 4: Post-transformation abstraction factor
        # - Compute average depth of top-level expressions.
        # - Count number of function and global variable names.
        # - Compute the average number of unique symbols per function.

        expr_depths: List[int] = []
        func_var_names: Set[str] = set()
        unique_syms: Dict[str, Set[str]] = {}
        for cc in compile_commands:
            os.chdir(cc.directory)
            # remove the first and last arguments since they are the compiler
            # name and the name of the file, and then fix the remaining
            # arguments
            args = compile_command.fix_args_for_clang(cc.arguments[1:-1])
            idx = clang.cindex.Index.create()
            tu: clang.cindex.TranslationUnit = idx.parse(cc.file, args)
            c: clang.cindex.Cursor = tu.cursor
            expr_depths += abstractometer.get_expr_depths(c)
            func_var_names |= abstractometer.get_func_var_names(c)
            unique_syms.update(abstractometer.get_unique_decls_refd_in_function_definitions(c))
            # TODO: test this and check that it actually works

        print('transformed avg expr nesting depth after:', (sum(expr_depths) / len(expr_depths)) if len(expr_depths) > 0 else 0)
        print('transformed num function and global names:', len(func_var_names))
        print('transformed avg unique symbols per function:',
          (sum([len(us) for us in unique_syms])
           / len(unique_syms))
          if len(unique_syms) > 0 else 0)

        # Flush to see evaluation results of this program before moving on to next one
        sys.stdout.flush()
        print()
        # Close out file
        # FIXME: use context manager instead
        ofp.close()
        # Change back to top-level evaluation directory
        os.chdir(evaluation_dir)


if __name__ == '__main__':
    main()
