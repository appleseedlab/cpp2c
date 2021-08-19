'''
main.py

Driver program
'''

import json
import sys
from dataclasses import asdict
from collect_macro_data import collect_macro_data


def main():
    if len(sys.argv) != 4:
        print("Please provide a CPP statistics file, the path to the analyzed C file, and the output JSON file")
        return
    stats_file, c_file, output_file = sys.argv[1:]
    if not output_file.endswith(".json"):
        print("Output file must be a .json file")
        return

    result = collect_macro_data(stats_file, c_file)
    with open(output_file, "w") as fp:
        json.dump(result, fp, default=asdict, indent=4)


if __name__ == '__main__':
    main()
