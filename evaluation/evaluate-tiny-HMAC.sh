#!/bin/bash

TINY_HMAC_REPO=tiny-HMAC-c-93bdfa8114a32cf25ba70cb1f0957d3bf0f180af
TINY_HMAC_ZIP=$TINY_HMAC_REPO.zip
TINY_HMAC_UNZIP_DIR=$TINY_HMAC_REPO
TINY_HMAC_DIR=tiny-HMAC
SRC_DIR=$TINY_HMAC_DIR/src

CSV_DIR=stats/tiny-HMAC

CPP2_C=../transformation_tool/build/bin/cpp-to-c

mkdir -p $CSV_DIR
rm -fr $TINY_HMAC_DIR

echo "Step 1: Unzipping Tiny HMAC to $TINY_HMAC_DIR"
unzip $TINY_HMAC_ZIP
mv $TINY_HMAC_UNZIP_DIR $TINY_HMAC_DIR

echo "Step 2: Transforming C files in $SRC_DIR"
for FILEPATH in $(ls $SRC_DIR/*.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2_C -fsyntax-only $FILEPATH -Xclang -plugin-arg-cpp-to-c -Xclang -overwrite-files 2> >(tail -n2 >$CSV_DIR/$FN_NO_EXT.csv)
done

echo "Step 3: Running Tiny HMAC tests"
cd $TINY_HMAC_DIR
# Change the python command to python2
sed -i 's/python/python2/' Makefile
make
make test