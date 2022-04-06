#!/bin/bash

PROJECT_NAME=bc
SOURCE_ZIP=bc-1.07.tar.gz
SOURCE_DIR=bc-1.07
SRC_DIR=$SOURCE_DIR/bc

CSV_DIR=stats/bc-1.07

CPP2_C=../implementation/build/bin/cpp2c

echo "Removing $SOURCE_DIR and recreating $CSV_DIR"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $SOURCE_DIR

if [ ! -f "$SOURCE_ZIP" ]; then
    wget https://mirrors.kernel.org/gnu/bc/bc-1.07.tar.gz
fi

echo "Unzipping $PROJECT_NAME to $SOURCE_DIR"
tar -xvf $SOURCE_ZIP

echo "Configuring $PROJECT_NAME"
cd $SOURCE_DIR
bash configure
# make
cd ..

echo "Transforming C files in $SRC_DIR"
for FILEPATH in $(ls $SRC_DIR/*.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2_C -fsyntax-only -I$SOURCE_DIR -I$SOURCE_DIR/h $FILEPATH -Xclang -plugin-arg-cpp2c -Xclang -overwrite-files -Xclang -plugin-arg-cpp2c -Xclang -dump-stats -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.csv -Xclang -plugin-arg-cpp2c -Xclang -dmds -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.json
done

# Exit prematurely unless arg passed to run tests
if [ $# -eq 0 ] || [ $1 != '-run-tests' ]; then
    exit
fi

echo "Running $PROJECT_NAME tests"
cd $SOURCE_DIR
make clean
make
make check
cd Test
bash timetest 1>/dev/null