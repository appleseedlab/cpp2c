'''gen-latex.py
reads the results data in the results directory and uses
the data to generate the code for latex tables
'''

import os
from typing import List, Union

Data = List[Union[str, int, float]]

RESULTS_DIR = r'results/'

NAME = 0
TIME_TO_BUILD = 1
AVG_EXPR_NESTING_DEPTH_AFTER = 2
NUM_FUNCTION_AND_GLOBAL_NAMES = 3
AVG_UNIQUE_SYMBOLS_PER_FUNCTION = 4
SOURCE_MACRO_DEFINITIONS = 5
SOURCE_MACRO_DEFINITIONS_OLMS = 6
SOURCE_MACRO_DEFINITIONS_FLMS = 7
EXPANDED_SOURCE_MACRO_DEFINITIONS = 8
EXPANDED_SOURCE_MACRO_DEFINITIONS_OLMS = 9
EXPANDED_SOURCE_MACRO_DEFINITIONS_FLMS = 10
UNIQUE_SOURCE_MACRO_EXPANSIONS = 11
TIME_TO_REACH_A_FIXED_POINT = 12
RUNS_TO_REACH_A_FIXED_POINT = 13
POTENTIALLY_TRANSFORMABLE_MACRO_DEFINITIONS = 14
POTENTIALLY_TRANSFORMABLE_MACRO_DEFINITIONS_OLMS = 15
POTENTIALLY_TRANSFORMABLE_MACRO_DEFINITIONS_FLMS = 16
TRANSFORMED_MACRO_DEFINITIONS = 17
TRANSFORMED_MACRO_DEFINITIONS_OLMS = 18
TRANSFORMED_MACRO_DEFINITIONS_FLMS = 19
UNTRANSFORMED_POTENTIALLY_TRANSFORMABLE_MACRO_DEFINITIONS = 20
TRANSFORMED_MACRO_DEFINITIONS_OLMS = 21
TRANSFORMED_MACRO_DEFINITIONS_FLMS = 22
NUMBER_OF_MACROS_TRANSFORMED_TO_VARS = 23
PERCENTAGE_INCREASE_IN_TRANSFORMED_MACROS_WITH_OUR_APPROACH = 24
CATEGORIES_OF_REASONS_NOT_TRANSFORMED = 25
SYNTACTIC_WELL_FORMEDNESS = 26
ENVIRONMENT_CAPTURE = 27
PARAMETER_SIDE_EFFECTS = 28
UNSUPPORTED_CONSTRUCT = 29
TURNED_OFF_CONSTRUCT = 30
MULTIPLE_CATEGORIES = 31
POTENTIALLY_TRANSFORMABLE_INVOCATIONS = 32
POTENTIALLY_TRANSFORMABLE_INVOCATIONS_OLMS = 33
POTENTIALLY_TRANSFORMABLE_INVOCATIONS_FLMS = 34
UNIQUE_TRANSFORMED_INVOCATIONS_IN_SOURCE_DEFINITIONS = 35
UNIQUE_TRANSFORMED_INVOCATIONS_IN_TRANSFORMED_DEFINITIONS = 36
TOTAL_UNIQUE_TRANSFORMED_INVOCATIONS = 37
TOTAL_UNIQUE_TRANSFORMED_INVOCATIONS_OLMS = 38
TOTAL_UNIQUE_TRANSFORMED_INVOCATIONS_FLMS = 39
TOP_FIVE_MOST_TRANSFORMED_MACROS = 40
MACROS_WITH_MOST_TRANSFORMED_TYPES = 41
UNTRANSFORMED_INVOCATIONS = 42
POTENTIALLY_TRANSFORMABLE_POLYMORPHIC_MACROS = 43
POTENTIALLY_TRANSFORMABLE_POLYMORPHIC_MACROS_OLMS = 44
POTENTIALLY_TRANSFORMABLE_POLYMORPHIC_MACROS_FLMS = 45
TRANSFORMED_POLYMORPHIC_MACROS = 46
TRANSFORMED_POLYMORPHIC_MACROS_OLMS = 47
TRANSFORMED_POLYMORPHIC_MACROS_FLMS = 48
twenty_pt_summary_of_transformed_types = 49
TRANSFORMED_AVG_EXPR_NESTING_DEPTH_AFTER = 50
TRANSFORMED_NUM_FUNCTION_AND_GLOBAL_NAMES = 51
TRANSFORMED_AVG_UNIQUE_SYMBOLS_PER_FUNCTION = 52

def read_data(data: str) -> Data:
    lines = data.split('\n')
    name = lines[0].split()[-1]
    time_to_build = float(lines[1].split()[-1])
    avg_expr_nesting_depth_after = float(lines[2].split()[-1])
    num_function_and_global_names = int(lines[3].split()[-1])
    avg_unique_symbols_per_function = float(lines[4].split()[-1])
    source_macro_definitions = int(lines[5].split()[-1])
    source_macro_definitions_olms = int(lines[6].split()[-1])
    source_macro_definitions_flms = int(lines[7].split()[-1])
    expanded_source_macro_definitions = int(lines[8].split()[-1])
    expanded_source_macro_definitions_olms = int(lines[9].split()[-1])
    expanded_source_macro_definitions_flms = int(lines[10].split()[-1])
    unique_source_macro_expansions = int(lines[11].split()[-1])
    time_to_reach_a_fixed_point = float(lines[12].split()[-1])
    runs_to_reach_a_fixed_point = int(lines[13].split()[-1])
    potentially_transformable_macro_definitions = int(lines[14].split()[-1])
    potentially_transformable_macro_definitions_olms = int(lines[15].split()[-1])
    potentially_transformable_macro_definitions_flms = int(lines[16].split()[-1])
    transformed_macro_definitions = int(lines[17].split()[-1])
    transformed_macro_definitions_olms = int(lines[18].split()[-1])
    transformed_macro_definitions_flms = int(lines[19].split()[-1])
    untransformed_potentially_transformable_macro_definitions = int(lines[20].split()[-1])
    untransformed_potentially_transformable_macro_definitions_olms = int(lines[21].split()[-1])
    untransformed_potentially_transformable_macro_definitions_flms = int(lines[22].split()[-1])
    number_of_macros_transformed_to_vars = int(lines[23].split()[-1])
    percentage_increase_in_transformed_macros_with_our_approach = float((lines[24].split()[-1])[:-1])
    # categories_of_reasons_not_transformed
    syntactic_well_formedness = int(lines[26].split()[-1])
    environment_capture = int(lines[27].split()[-1])
    parameter_side_effects = int(lines[28].split()[-1])
    unsupported_construct = int(lines[29].split()[-1])
    turned_off_construct = int(lines[30].split()[-1])
    multiple_categories = int(lines[31].split()[-1])
    potentially_transformable_invocations = int(lines[32].split()[-1])
    potentially_transformable_invocations_olms = int(lines[33].split()[-1])
    potentially_transformable_invocations_flms = int(lines[34].split()[-1])
    unique_transformed_invocations_in_source_definitions = int(lines[35].split()[-1])
    unique_transformed_invocations_in_transformed_definitions = int(lines[36].split()[-1])
    total_unique_transformed_invocations = int(lines[37].split()[-1])
    total_unique_transformed_invocations_olms = int(lines[38].split()[-1])
    total_unique_transformed_invocations_flms = int(lines[39].split()[-1])
    # top_five_most_transformed_macros
    untransformed_invocations = int(lines[41].split()[-1])
    potentially_transformable_polymorphic_macros = int(lines[42].split()[-1])
    potentially_transformable_polymorphic_macros_olms = int(lines[43].split()[-1])
    potentially_transformable_polymorphic_macros_flms = int(lines[44].split()[-1])
    transformed_polymorphic_macros = int(lines[45].split()[-1])
    transformed_polymorphic_macros_olms = int(lines[46].split()[-1])
    transformed_polymorphic_macros_flms = int(lines[47].split()[-1])
    # twenty_pt_summary_of_transformed_types
    # macros_with_most_transformed_types
    transformed_avg_expr_nesting_depth_after = float(lines[50].split()[-1])
    transformed_num_function_and_global_names = int(lines[51].split()[-1])
    transformed_avg_unique_symbols_per_function = float(lines[52].split()[-1])

    return [
        name,
        time_to_build,
        avg_expr_nesting_depth_after,
        num_function_and_global_names,
        avg_unique_symbols_per_function,
        source_macro_definitions,
        source_macro_definitions_olms,
        source_macro_definitions_flms,
        expanded_source_macro_definitions,
        expanded_source_macro_definitions_olms,
        expanded_source_macro_definitions_flms,
        unique_source_macro_expansions,
        time_to_reach_a_fixed_point,
        runs_to_reach_a_fixed_point,
        potentially_transformable_macro_definitions,
        potentially_transformable_macro_definitions_olms,
        potentially_transformable_macro_definitions_flms,
        transformed_macro_definitions,
        transformed_macro_definitions_olms,
        transformed_macro_definitions_flms,
        untransformed_potentially_transformable_macro_definitions,
        untransformed_potentially_transformable_macro_definitions_olms,
        untransformed_potentially_transformable_macro_definitions_flms,
        number_of_macros_transformed_to_vars,
        percentage_increase_in_transformed_macros_with_our_approach,
        -1, # categories_of_reasons_not_transformed
        syntactic_well_formedness,
        environment_capture,
        parameter_side_effects,
        unsupported_construct,
        turned_off_construct,
        multiple_categories,
        potentially_transformable_invocations,
        potentially_transformable_invocations_olms,
        potentially_transformable_invocations_flms,
        unique_transformed_invocations_in_source_definitions,
        unique_transformed_invocations_in_transformed_definitions,
        total_unique_transformed_invocations,
        total_unique_transformed_invocations_olms,
        total_unique_transformed_invocations_flms,
        -1, # top_five_most_transformed_macros
        untransformed_invocations,
        potentially_transformable_polymorphic_macros,
        potentially_transformable_polymorphic_macros_olms,
        potentially_transformable_polymorphic_macros_flms,
        transformed_polymorphic_macros,
        transformed_polymorphic_macros_olms,
        transformed_polymorphic_macros_flms,
        -1, # twenty_pt_summary_of_transformed_types
        -1, # macros_with_most_transformed_types
        transformed_avg_expr_nesting_depth_after,
        transformed_num_function_and_global_names,
        transformed_avg_unique_symbols_per_function,
    ]


def percent_flm_transformed(d: Data) -> float:
    return round((  d[TRANSFORMED_MACRO_DEFINITIONS_FLMS]
                    / d[POTENTIALLY_TRANSFORMABLE_MACRO_DEFINITIONS_FLMS]
                    * 100),
                2)

def avg_percent_flm_transformed(all_data: List[Data]) -> float:
    return round((  sum([percent_flm_transformed(d) for d in all_data])
                    / len(all_data)),
                2   )

def table_percent_function_like_transformed(all_data: List[Data]) -> str:
    return '\n'.join(
        [
            r'\begin{table}[htbp]',
            r'\caption{Percent of transformable function-like macros transformed.}',
            r'\label{tab:pcnt-flsm-trans}',
            r'\begin{tabular}{ |l|l| }',
            r'\hline',
            r'program name  &   \% transformed flms \\',
            r'\hline\hline',
            '\t\\\\\n'.join(['\t&\t'.join([d[NAME], str(percent_flm_transformed(d))]) for d in all_data]) + '\t\\\\',
            r'\hline',
            f'average   &   {avg_percent_flm_transformed(all_data)} \\\\',
            r'\hline',
            r'\end{tabular}',
            r'\end{table}'
        ])

def main():
    all_data = []
    files = [os.path.join(RESULTS_DIR, f) for f in os.listdir(RESULTS_DIR)]
    files.sort()
    for f in files:
        with open(f) as fp:
            d = read_data(fp.read())
            # change mosaic's name to be shorter
            if 'mosaic' in d[NAME]:
                d[NAME] = 'mosaic-2.7'
            # change remind's name to include version number
            if 'remind' in d[NAME]:
                d[NAME] = 'remind-4.00.01'
            all_data.append(d)

    print(table_percent_function_like_transformed(all_data))



if __name__ == '__main__':
    main()