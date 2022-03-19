#!/bin/bash

# Runs the evaluation of Cpp2C

# Clear the stats folder
rm -fr stats/*

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
for DIR in $(find stats/* -type d); do
    python3 aggregate_program_stats.py $DIR > $DIR.csv
    if [ $? = 1 ]; then
        echo "Error aggregating data for directory $DIR"
    fi
done

# Aggregate transformation data of all programs into a single CSV file
