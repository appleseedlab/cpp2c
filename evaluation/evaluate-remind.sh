#!/bin/bash

REMIND_ZIP=remind-03.04.02.tar.gz
REMIND_DIR=remind-03.04.02
SRC_DIR=$REMIND_DIR/src

CSV_DIR=stats/remind-03.04.02

CPP2_C=../transformation_tool/build/bin/cpp-to-c

echo "Step 0: Remove old unzipped directory, and clear/create stats directory"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $REMIND_DIR

echo "Step 1: Unzipping Remind to $REMIND_DIR"
tar -xvf $REMIND_ZIP

echo "Step 2: Transforming C files in $SRC_DIR"
for FILEPATH in $(ls $SRC_DIR/*.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2_C -fsyntax-only $FILEPATH -Xclang -plugin-arg-cpp-to-c -Xclang -overwrite-files -Xclang -plugin-arg-cpp-to-c -Xclang -dump-stats -Xclang -plugin-arg-cpp-to-c -Xclang $CSV_DIR/$FN_NO_EXT.csv
done


echo "Step 3: Running Remind tests"
cd $REMIND_DIR
make
make test
