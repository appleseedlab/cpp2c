'''aggregate_program_stats.py

Aggregates transformation data for an evaluation program into a single CSV file
'''

import csv
import os
import sys
from collections import defaultdict
from statistics import mean
from typing import DefaultDict, Dict, List

TOTAL_EXPANSIONS_HEADER = 'Top Level Expansions In Main File'
SUCCESSFUL_TRANSFORMATIONS_HEADER = 'Successfully Transformed Top Level Expansions'
PERCENT_TRANSFORMED_HEADER = 'Percentage of Expansions Transformed'
NUM_FILES_PROCESSED_HEADER = 'Number of Files Processed'
TRANSFORMATION_TIME_HEADER = 'Transformation Time (ms)'
AVG_TRANSFORMATION_TIME_HEADER = 'Average Transformation Time (ms)'
AVG_EXPANSIONS_PER_FILE = 'Average Top Level Expansions per File'
FILE_SIZE_HEADER = 'File Size (bytes)'
AVG_FILE_SIZE_HEADER = 'Average File Size (bytes)'


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


def rounded_mean_or_zero(data: List[int]) -> int:
    '''Returns the arithmetic mean of the data, or 0 if the data is empty'''
    return round(mean(data)) if data != [] else 0


def main():
    if len(sys.argv) < 2:
        print('USAGE: python3 aggregate_program_stats.py PROGRAM_DIR',
              file=sys.stderr)
        exit(1)
    evaluation_program = sys.argv[1]
    filenames = os.listdir(evaluation_program)

    # Collect stats of all transformed files into one CSV
    aggregated: DefaultDict[str, int] = defaultdict(int)
    file_stat_dicts = [
        one_row_csv_to_dict(os.path.join(evaluation_program, filename))
        for filename in filenames]
    for file_stat_dict in file_stat_dicts:
        sum_dict_vals(aggregated, file_stat_dict)

    # Record the percentage of expansions successfully transformed
    total_expansions = aggregated[TOTAL_EXPANSIONS_HEADER]
    transformed_expansions = aggregated[SUCCESSFUL_TRANSFORMATIONS_HEADER]
    percent_transformed = 0
    if total_expansions > 0:
        percent_transformed = transformed_expansions / total_expansions
        percent_transformed *= 100
        percent_transformed = round(percent_transformed)
    aggregated[PERCENT_TRANSFORMED_HEADER] = percent_transformed

    # Record the number of files processed
    aggregated[NUM_FILES_PROCESSED_HEADER] = len(filenames)

    # Record the average file transformation time
    transformation_times = [
        d[TRANSFORMATION_TIME_HEADER] for d in file_stat_dicts]
    avg_transformation_time = rounded_mean_or_zero(transformation_times)
    aggregated[AVG_TRANSFORMATION_TIME_HEADER] = avg_transformation_time

    # Record the average number of expansions per file
    expansions_per_file = [
        d[TOTAL_EXPANSIONS_HEADER] for d in file_stat_dicts]
    avg_expansions_per_file = rounded_mean_or_zero(expansions_per_file)
    aggregated[AVG_EXPANSIONS_PER_FILE] = avg_expansions_per_file

    # Record the average file size
    file_sizes = [
        d[FILE_SIZE_HEADER] for d in file_stat_dicts]
    avg_file_size = rounded_mean_or_zero(file_sizes)
    aggregated[AVG_FILE_SIZE_HEADER] = avg_file_size

    # Print the dict in CSV format
    keys = aggregated.keys()
    print(*keys, sep=", ")
    print(*[aggregated[k] for k in keys], sep=", ")


if __name__ == '__main__':
    main()
