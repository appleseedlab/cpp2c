#!/bin/bash

REMIND_ZIP=remind-03.04.02.tar.gz
REMIND_DIR=remind-03.04.02
SRC_DIR=$REMIND_DIR/src

CSV_DIR=stats/remind-03.04.02

CPP2_C=../implementation/build/bin/cpp2c

echo "Removing $REMIND_DIR and recreating $CSV_DIR"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $REMIND_DIR

if [ ! -f "$REMIND_ZIP" ]; then
    echo "Downloading Remind"
    wget https://dianne.skoll.ca/projects/remind/download/remind-03.04.02.tar.gz
fi

echo "Unzipping Remind to $REMIND_DIR"
tar -xvf $REMIND_ZIP

echo "Configure remind so that config.h is available"
cd $REMIND_DIR
bash configure
cd ..

echo "Transforming C files in $SRC_DIR"
for FILEPATH in $(ls $SRC_DIR/*.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2_C -fsyntax-only $FILEPATH -Xclang -plugin-arg-cpp2c -Xclang -overwrite-files -Xclang -plugin-arg-cpp2c -Xclang -dump-stats -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.csv -Xclang -plugin-arg-cpp2c -Xclang -dmds -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.json
done

# Exit prematurely unless arg passed to run tests
if [ $# -eq 0 ] || [ $1 != '-run-tests' ]; then
    exit
fi

echo "Running Remind tests"
cd $REMIND_DIR
make clean
make
make test
