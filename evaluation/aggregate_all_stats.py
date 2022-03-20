'''aggregate_all_stats.py

Aggregates transformation data for each evaluation program's aggregated stats
into a single CSV file.
'''

import os
import sys


def main():
    if len(sys.argv) < 2:
        print("USAGE: python3 aggregate_all_stats.py STATS_DIR", file=sys.stderr)
        exit(1)
    stats_dir = sys.argv[1]

    # Traverse all evaluation program CSV files
    printed_headers = False
    for filename in os.listdir(stats_dir):
        # Only check CSV files
        if not filename.endswith('.csv'):
            continue

        # Print the headers for the output, with the program name added to
        # the list of headers
        program_name = filename[:-len('.csv')]
        filepath = os.path.join(stats_dir, filename)
        with open(filepath) as fp:
            lines = fp.readlines()
            if not printed_headers:
                print("Evaluation Program,", lines[0], end="")
                printed_headers = True
            print(program_name + ',', lines[1], end="")


if __name__ == '__main__':
    main()
