'''
main.py

Driver program for macro data collector
'''

import json
import sys
from dataclasses import asdict
from typing import List

from macro_classifier.classifications import SimpleExpressionMacro
from macro_classifier.classify_macros import check_macro_usage, classify_macro
from macro_data_collector.collect_macro_data import collect_macro_data


def main():
    if len(sys.argv) != 3:
        print("Please provide the path to the C file and the output JSON file")
        return
    c_file, output_file = sys.argv[1:]
    if not output_file.endswith(".json"):
        print("Output file must be a .json file")
        return

    macro_data = collect_macro_data(c_file)

    classified_macros = [classify_macro(macro) for macro in macro_data]
    check_macro_usage(classified_macros, c_file)

    with open(output_file, "w") as fp:
        json.dump(classified_macros, fp, default=asdict, indent=4)

    enum_names_to_macros = {}

    for simple_macro in [cm for cm in classified_macros
                         if isinstance(cm, SimpleExpressionMacro)
                         and cm.used_as_case_label]:
        if enum_names_to_macros.get(simple_macro.enum_group_name) is None:
            enum_names_to_macros[simple_macro.enum_group_name] = []
        enum_names_to_macros[simple_macro.enum_group_name].append(simple_macro)

    c_file_lines: List[str]
    with open(c_file) as fp:
        c_file_lines = [line.strip("\n") for line in fp.readlines()]

    # TODO: Perhaps move the emission of converted macros to a function?
    for cm in classified_macros:
        emit_line = cm.macro.start_line - 1
        if isinstance(cm, SimpleExpressionMacro):
            if cm.emitted:
                c_file_lines[emit_line] = ''
                continue
            if cm.used_as_case_label:
                macros_in_group = enum_names_to_macros[cm.enum_group_name]
                emitted_macros = [m.emit()for m in macros_in_group]
                emitted_enum = ("enum "
                                + cm.enum_group_name
                                + "{"
                                + ', '.join(emitted_macros)
                                + "};"
                                )
                c_file_lines[emit_line] = emitted_enum
            else:
                c_file_lines[cm.macro.start_line - 1] = cm.emit()
                for i in range(cm.macro.start_line, cm.macro.end_line):
                    c_file_lines[i] = ""

    print('\n'.join(c_file_lines))


if __name__ == '__main__':
    main()
