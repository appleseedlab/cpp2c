#!/bin/bash

PROGRAM_NAME=gzip
PROGRAM_ZIP=gzip-1.10.tar.gz
PROGRAM_DIR=gzip-1.10
PROGRAM_LINK=https://gnu.mirror.constant.com/gzip/gzip-1.10.tar.gz
SRC_DIR=$PROGRAM_DIR

CSV_DIR=stats/gzip-1.10

CPP2_C=../implementation/build/bin/cpp2c

echo "Removing $PROGRAM_DIR and recreating $CSV_DIR"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $PROGRAM_DIR

if [ ! -f "$PROGRAM_ZIP" ]; then
    wget "$PROGRAM_LINK"
fi

echo "Unzipping $PROGRAM_NAME to $PROGRAM_DIR"
tar -xvf $PROGRAM_ZIP

echo "Configuring $PROGRAM_NAME"
cd $PROGRAM_DIR
bash configure
# make
cd ..

echo "Transforming C files in $SRC_DIR"
for FILEPATH in $(ls $SRC_DIR/*.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2_C -fsyntax-only -I$PROGRAM_DIR/lib $FILEPATH -Xclang -plugin-arg-cpp2c -Xclang -overwrite-files -Xclang -plugin-arg-cpp2c -Xclang -dump-stats -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.csv -Xclang -plugin-arg-cpp2c -Xclang -dmds -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.json
done

# Exit prematurely unless arg passed to run tests
if [ $# -eq 0 ] || [ $1 != '-run-tests' ]; then
    exit
fi

echo "Running $PROGRAM_NAME tests"
cd $PROGRAM_DIR
make clean
make
make check