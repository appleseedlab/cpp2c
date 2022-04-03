'''aggregate_program_stats.py

Aggregates transformation data for an evaluation program into a single CSV file
'''

import csv
import json
import os
import sys
from collections import defaultdict
from statistics import mean
from typing import DefaultDict, Dict, List, Set


def print_dict_as_csv(d: Dict, file=sys.stdout) -> None:
    keys = d.keys()
    print(*keys, sep=", ", file=file)
    print(*[d[k] for k in keys], sep=", ", file=file)


def json_to_dict(filename: str) -> Dict:
    with open(filename) as fp:
        return json.load(fp)


def one_row_csv_to_dict(filename: str) -> Dict[str, int]:
    '''
    Deserializes a one-row CSV file whose values are all integers into a Dict
    '''
    with open(filename, newline='') as fp:
        reader = csv.DictReader(fp,)
        first_row = next(reader)
        return {k.strip(): int(first_row[k]) for k in reader.fieldnames}


def sum_dict_vals(lhs: DefaultDict[str, int], rhs: Dict[str, int]) -> None:
    '''
    Adds to the value of each key in lhs with the value associated with
    it in rhs, or adds the key in rhs to lhs if it does not exist
    '''
    for k in rhs:
        lhs[k] += rhs[k]


def union_dict_vals(lhs: DefaultDict[str, Set[str]], rhs: Dict[str, Set[str]]) -> None:
    '''
    Unions the sets of each key in lhs with the set associated with
    it in rhs, or adds the key in rhs to lhs if it does not exist
    '''
    for k in rhs:
        lhs[k] |= rhs[k]


def rounded_mean_or_zero(data: List[int], ndigits: int = None) -> int:
    '''Returns the arithmetic mean of the data, or 0 if the data is empty'''
    return round(mean(data), ndigits) if data != [] else 0


def main():
    if len(sys.argv) < 2:
        print(
            'USAGE: python3 aggregate_program_stats.py EVALUATION_RESULTS_DIR',
            file=sys.stderr)
        exit(1)
    evaluation_results_dir = sys.argv[1]
    filenames = os.listdir(evaluation_results_dir)

    # Collect stats of all transformed files into one CSV
    aggregated_csv: DefaultDict[str, int] = defaultdict(int)
    csv_file_stat_dicts = [
        one_row_csv_to_dict(os.path.join(evaluation_results_dir, filename))
        for filename in filenames
        if filename.endswith(".csv")]
    for file_stat_dict in csv_file_stat_dicts:
        sum_dict_vals(aggregated_csv, file_stat_dict)

    # Collect number of transformed definitions for each original definition
    # into one JSON
    aggregated_json: DefaultDict[str, set] = defaultdict(set)
    json_file_stat_dicts = [
        json_to_dict(os.path.join(evaluation_results_dir, filename))
        for filename in filenames
        if filename.endswith(".json")]
    # Convert transformed prototype lists to sets
    for k, v in aggregated_json.items():
        aggregated_json[k] = set(v)
    for file_stat_dict in json_file_stat_dicts:
        # Convert transformed prototype lists to sets
        for k, v in file_stat_dict.items():
            file_stat_dict[k] = set(v)
        union_dict_vals(aggregated_json, file_stat_dict)

    # Record definition stats

    aggregated_csv['Original Definitions Found'] = \
        len(aggregated_json.keys())

    aggregated_csv['Original OLM Definitions Found'] = \
        len([k for k in aggregated_json.keys() if k.startswith('ObjectLike')])

    aggregated_csv['Original FLM Definitions Found'] = \
        len([k for k in aggregated_json.keys() if k.startswith('FunctionLike')])

    aggregated_csv['Unique Emitted Transformed Definitions'] = \
        sum([len(v) for v in aggregated_json.values()])

    aggregated_csv['Unique Emitted Transformed OLM Definitions'] = \
        sum([len(v) for k, v in aggregated_json.items() if k.startswith('ObjectLike')])

    aggregated_csv['Unique Emitted Transformed FLM Definitions'] = \
        sum([len(v) for k, v in aggregated_json.items()
            if k.startswith('FunctionLike')])

    aggregated_csv['Avg # of Unique Defs Emitted per Original Def'] = \
        rounded_mean_or_zero(
            [len(v) for v in aggregated_json.values()], 2)

    aggregated_csv['Avg # of Unique Defs Emitted per Original OLM Def'] = \
        rounded_mean_or_zero(
            [len(v) for k, v in aggregated_json.items() if k.startswith('ObjectLike')], 2)

    aggregated_csv['Avg # of Unique Defs Emitted per Original FLM Def'] = \
        rounded_mean_or_zero(
            [len(v) for k, v in aggregated_json.items() if k.startswith('FunctionLike')], 2)

    aggregated_csv['Avg # of Unique Defs Emitted per Original Def that was Transformed At Least Once'] = \
        rounded_mean_or_zero(
            [len(v) for v in aggregated_json.values() if len(v) > 0], 2)

    aggregated_csv['Avg # of Unique Defs Emitted per Original OLM Def that was Transformed At Least Once'] = \
        rounded_mean_or_zero(
            [len(v) for k, v in aggregated_json.items() if k.startswith('ObjectLike') and len(v) > 0], 2)

    aggregated_csv['Avg # of Unique Defs Emitted per Original FLM Def that was Transformed At Least Once'] = \
        rounded_mean_or_zero(
            [len(v) for k, v in aggregated_json.items() if k.startswith('FunctionLike') and len(v) > 0], 2)

    aggregated_csv['Greatest Number of Unique Defs Emitted per Original Def'] = \
        max([len(v) for v in aggregated_json.values()])

    aggregated_csv['Greatest Number of Unique Defs Emitted per Original OLM Def'] = \
        max([len(v) for k, v in aggregated_json.items() if k.startswith('ObjectLike')])

    aggregated_csv['Greatest Number of Unique Defs Emitted per Original FLM Def'] = \
        max([len(v) for k, v in aggregated_json.items()
            if k.startswith('FunctionLike')])

    # Print the dict in CSV format
    print_dict_as_csv(aggregated_csv)


if __name__ == '__main__':
    main()
