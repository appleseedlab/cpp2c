#!/bin/bash

# Runs the evaluation of Cpp2C

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
    
    # Run the evaluation
    echo "Evaluating $PROJECT_NAME"

    # Make the directory to store the aggregated results for this run
    mkdir -p $PROJECT_AGGREGATED_RESULTS_DIR
    bash ./$SCRIPT 1>/dev/null
    
    # Aggregate the transformation data for the program a single CSV file
    python3 aggregate_program_stats.py $STATS_DIR/$PROJECT_NAME > $PROJECT_AGGREGATED_RESULTS_DIR/$PROJECT_NAME.csv
done

# Aggregate transformation data of all programs into a single CSV file
echo "Aggregating evaluation results for all projects"
mkdir -p $ALL_AGGREGATED_RESULTS_DIR
ALL_STATS_FILE=$ALL_AGGREGATED_RESULTS_DIR/all_stats.csv
python3 aggregate_all_stats.py $PROJECT_AGGREGATED_RESULTS_DIR > $ALL_STATS_FILE
