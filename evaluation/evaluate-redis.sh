#!/bin/bash

REDIS_ZIP=redis-6.2.6.zip
REDIS_DIR=redis-6.2.6
SRC_DIR=$REDIS_DIR/src

CSV_DIR=stats/redis-03.04.02

CPP2_C=../transformation_tool/build/bin/cpp2c

mkdir -p $CSV_DIR
rm -fr $REDIS_DIR

echo "Step 0: Remove old unzipped directory, and clear/create stats directory"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $REDIS_DIR

echo "Step 1: Unzipping Redis to $REDIS_DIR"
unzip $REDIS_ZIP

echo "Step 2: Transforming C files in $SRC_DIR"
for FILEPATH in $(find redis-6.2.6/src/ -type f -name *.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2_C -fsyntax-only $FILEPATH -Xclang -plugin-arg-cpp2c -Xclang -overwrite-files -Xclang -plugin-arg-cpp2c -Xclang -dump-stats -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.csv
done

echo "Step 3: Running Redis tests"
cd $REDIS_DIR
make
./runtest
./runtest-cluster
./runtest-moduleapi
./runtest-sentinel
