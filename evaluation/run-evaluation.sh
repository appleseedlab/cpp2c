#!/bin/bash

# Runs the evaluation of Cpp2C

STATS_DIR=stats

# Clear the stats folder
rm -fr $STATS_DIR/*

# Run the evaluation scripts
for FN in $(ls evaluate-*.sh); do
    # Skip Redis for now
    if [ $FN = 'evaluate-redis.sh' ]; then
        continue
    fi
    # Run the evaluation script
    $(bash $FN)
done

# Aggregate the transformation data of each program into a single CSV file each
for DIR in $(find $STATS_DIR/* -type d); do
    python3 aggregate_program_stats.py $DIR > $DIR.csv
    if [ $? != 0 ]; then
        echo "Error aggregating data for directory $DIR"
    fi
done

# Aggregate transformation data of all programs into a single CSV file
python3 aggregate_all_stats.py > all_stats.csv