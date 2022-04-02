#!/bin/bash

TINY_LINT_ZIP=4de8b64c97fda3117a7ddc9895a30adb97fbae97.zip
TINY_LINT_DIR=tiny-lint-c-4de8b64c97fda3117a7ddc9895a30adb97fbae97
SRC_DIR=$TINY_LINT_DIR/src

CSV_DIR=stats/tiny-lint

CPP2_C=../implementation/build/bin/cpp2c

echo "Removing $TINY_LINT_DIR and recreating $CSV_DIR"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $TINY_LINT_DIR

if [ ! -f "$TINY_LINT_ZIP" ]; then
    echo "Downloading Tiny Lint"
    wget https://github.com/kokke/tiny-lint-c/archive/4de8b64c97fda3117a7ddc9895a30adb97fbae97.zip
fi

echo "Unzipping Tiny Lint to $TINY_LINT_DIR"
unzip $TINY_LINT_ZIP

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

echo "Running Tiny Lint tests"
cd $TINY_LINT_DIR
make
make test