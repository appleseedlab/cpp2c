'''
main.py

Driver program for macro data collector
'''

import json
from typing import List
from macro_classifier.classifications import SimpleConstantMacro, SimplePassByValueFunctionMacro
from macro_classifier.classify_macros import classify_macro
import sys
from dataclasses import asdict
from macro_data_collector.collect_macro_data import collect_macro_data


def main():
    if len(sys.argv) != 4:
        print("Please provide a CPP statistics file, the path to the analyzed C file, and the output JSON file")
        return
    stats_file, c_file, output_file = sys.argv[1:]
    if not output_file.endswith(".json"):
        print("Output file must be a .json file")
        return

    macro_data = collect_macro_data(stats_file, c_file)

    classified_macros = [classify_macro(macro) for macro in macro_data]

    with open(output_file, "w") as fp:
        json.dump(classified_macros, fp, default=asdict, indent=4)

    c_file_lines: List[str]
    with open(c_file) as fp:
        c_file_lines = fp.readlines()
    for cm in classified_macros:
        if isinstance(cm, SimpleConstantMacro) or isinstance(cm, SimplePassByValueFunctionMacro):
            c_file_lines[cm.macro.start_line - 1] = cm.emit()
            for i in range(cm.macro.start_line, cm.macro.end_line):
                c_file_lines[i] = ""

    print('\n'.join(c_file_lines))


if __name__ == '__main__':
    main()
