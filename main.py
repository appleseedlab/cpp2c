'''
main.py

Driver program for macro data collector
'''

import json
import sys
from dataclasses import asdict

from macro_fact_collector.collect_macro_facts import collect_macro_facts


def main():
    if len(sys.argv) != 3:
        print("Please provide the path to the C file and the output JSON file")
        return
    c_file, output_file = sys.argv[1:]
    if not output_file.endswith(".json"):
        print("Output file must be a .json file")
        return

    macro_facts = collect_macro_facts(c_file)

    with open(output_file, "w") as fp:
        json.dump(macro_facts, fp, default=asdict, indent=4)


if __name__ == '__main__':
    main()
