for FN in $(ls -d */); do
    ./collect_macro_definition_stats.sh $FN > $(basename $FN).csv
done

tail -v -n +1 *.csv > macro_definition_stats.txt