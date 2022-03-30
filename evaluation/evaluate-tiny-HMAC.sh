#!/bin/bash

TINY_HMAC_ZIP=93bdfa8114a32cf25ba70cb1f0957d3bf0f180af.zip
TINY_HMAC_DIR=tiny-HMAC-c-93bdfa8114a32cf25ba70cb1f0957d3bf0f180af
SRC_DIR=$TINY_HMAC_DIR/src

CSV_DIR=stats/tiny-HMAC

CPP2_C=../implementation/build/bin/cpp2c

echo "Removing $TINY_HMAC_DIR and recreating $CSV_DIR"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $TINY_HMAC_DIR

if [ ! -f "$TINY_HMAC_ZIP" ]; then
    echo "Downloading Tiny HMAC"
    wget https://github.com/kokke/tiny-HMAC-c/archive/93bdfa8114a32cf25ba70cb1f0957d3bf0f180af.zip
fi

echo "Unzipping Tiny HMAC to $TINY_HMAC_DIR"
unzip $TINY_HMAC_ZIP

echo "Transforming C files in $SRC_DIR"
for FILEPATH in $(ls $SRC_DIR/*.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2_C -fsyntax-only $FILEPATH -Xclang -plugin-arg-cpp2c -Xclang -overwrite-files -Xclang -plugin-arg-cpp2c -Xclang -dump-stats -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.csv
done

# Exit prematurely unless arg passed to run tests
if [ $# -eq 0 ] || [ $1 != '-run-tests' ]; then
    exit
fi

echo "Running Tiny HMAC tests"
cd $TINY_HMAC_DIR
# Change the python command to python2
sed -i 's/python/python2/' Makefile
make
make test