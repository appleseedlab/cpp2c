#!/bin/bash

# Runs the evaluation of Cpp2C

NUM_WARMUP_RUNS=3
NUM_EVALUATION_RUNS=5
STATS_DIR=stats
PROJECT_AGGREGATED_RESULTS_DIR=$STATS_DIR/project_aggregated_results
ALL_AGGREGATED_RESULTS_DIR=$STATS_DIR/all_aggregated_results

declare -A EVALUATION_SCRIPT_PROJECT_DIR=(
    ["evaluate-tiny-regex.sh"]="tiny-regex"
    ["evaluate-tiny-HMAC.sh"]="tiny-HMAC"
    ["evaluate-tiny-lint.sh"]="tiny-lint"
    ["evaluate-remind.sh"]="remind-03.04.02"
    ["evaluate-lua.sh"]="lua-5.4.4"
)

# Clear the stats folder
rm -fr $STATS_DIR
mkdir -p $STATS_DIR

# Run the evaluation scripts
for SCRIPT in ${!EVALUATION_SCRIPT_PROJECT_DIR[@]}; do

    PROJECT_NAME=${EVALUATION_SCRIPT_PROJECT_DIR[$SCRIPT]}

    # Warm up the evaluation
    echo "Warming up $PROJECT_NAME with $NUM_WARMUP_RUNS transformation runs"
    for (( i=1; i <= $NUM_WARMUP_RUNS; i++)); do
        echo "$PROJECT_NAME: Warmup run $i/$NUM_WARMUP_RUNS"
        bash ./$SCRIPT 1>/dev/null
    done

    # Run the evaluation
    echo "Evaluating $PROJECT_NAME with $NUM_EVALUATION_RUNS transformation runs"
    for (( i=1; i <= $NUM_EVALUATION_RUNS; i++)); do
        # Make the directory to store the aggregated results for this run
        RESULTS_DIR=$PROJECT_AGGREGATED_RESULTS_DIR\_$i
        mkdir -p $RESULTS_DIR
        echo "$PROJECT_NAME: Evaluation run $i/$NUM_EVALUATION_RUNS"
        bash ./$SCRIPT 1>/dev/null
        # Aggregate the transformation data for the program a single CSV file
        echo "$PROJECT_NAME: Aggregating data for run $i/$NUM_EVALUATION_RUNS"
        python3 aggregate_program_stats.py $STATS_DIR/$PROJECT_NAME > $RESULTS_DIR/$PROJECT_NAME.csv
    done
done

# Aggregate transformation data of all programs into a single CSV file
mkdir -p $ALL_AGGREGATED_RESULTS_DIR
for (( i=1; i <= $NUM_EVALUATION_RUNS; i++)); do
    echo "Aggregating evaluation results for run $i/$NUM_EVALUATION_RUNS of all projects"
    RUN_RESULTS_DIR=$PROJECT_AGGREGATED_RESULTS_DIR\_$i
    ALL_STATS_FILE=$ALL_AGGREGATED_RESULTS_DIR/all_stats_$i.csv
    python3 aggregate_all_stats.py $RUN_RESULTS_DIR > $ALL_STATS_FILE
done

# TODO: Take arithmetic/geometric mean of aggregated results across all runs
# and store in another file