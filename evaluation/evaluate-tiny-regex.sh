#!/bin/bash

TINY_REGEX_REPO=tiny-regex-c-2d306a5a71128853d18292e8bb85c8e745fbc9d0
TINY_REGEX_ZIP=$TINY_REGEX_REPO.zip
TINY_REGEX_UNZIP_DIR=$TINY_REGEX_REPO
TINY_REGEX_DIR=tiny-regex

CSV_DIR=stats/tiny-regex

CPP2_C=../transformation_tool/build/bin/cpp2c

echo "Removing $TINY_REGEX_DIR and recreating $CSV_DIR"
rm -fr $CSV_DIR
mkdir -p $CSV_DIR
rm -fr $TINY_REGEX_DIR

echo "Unzipping Tiny Regex to $TINY_REGEX_DIR"
unzip $TINY_REGEX_ZIP
mv $TINY_REGEX_UNZIP_DIR $TINY_REGEX_DIR

echo "Transforming $TINY_REGEX_DIR/re.c"
$CPP2_C -fsyntax-only $TINY_REGEX_DIR/re.c -Xclang -plugin-arg-cpp2c -Xclang -overwrite-files -Xclang -plugin-arg-cpp2c -Xclang -dump-stats -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/re.csv

# Exit prematurely unless arg passed to run tests
if [ $# -eq 0 ] || [ $1 != '-run-tests' ]; then
    exit
fi

echo "Running Tiny Regex tests"
cd $TINY_REGEX_DIR
make
./tests/test_compile && ./tests/test1 && ./tests/test2