#!/bin/bash

LUA_ZIP=lua-5.4.4.tar.gz
LUA_DIR=lua-5.4.4
TEST_ZIP=lua-5.4.4-tests.tar.gz
TEST_DIR=lua-5.4.4-tests
SRC_DIR=$LUA_DIR/src

CSV_DIR=stats/lua-5.4.4

CPP2C=../implementation/build/bin/cpp2c

mkdir -p $CSV_DIR
rm -fr $LUA_DIR

echo "Removing $LUA_DIR and $TEST_DIR, and recreating $CSV_DIR"
rm -fr $LUA_DIR
rm -fr $TEST_DIR
rm -fr $CSV_DIR
mkdir -p $CSV_DIR

if [ ! -f "$LUA_ZIP" ]; then
    echo "Downloading Lua"
    wget https://www.lua.org/ftp/lua-5.4.4.tar.gz
fi

echo "Unzipping Lua to $LUA_DIR"
tar -xvf $LUA_ZIP

echo "Transforming C files in $SRC_DIR"
for FILEPATH in $(find $SRC_DIR -type f -name *.c); do
    FN=$(basename $FILEPATH)
    FN_NO_EXT=${FN%.c}
    echo "Transforming $FILEPATH"
    $CPP2C -fsyntax-only $FILEPATH -Xclang -plugin-arg-cpp2c -Xclang -overwrite-files -Xclang -plugin-arg-cpp2c -Xclang -dump-stats -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.csv -Xclang -plugin-arg-cpp2c -Xclang -dmds -Xclang -plugin-arg-cpp2c -Xclang $CSV_DIR/$FN_NO_EXT.json
done

# Exit prematurely unless arg passed to run tests
if [ $# -eq 0 ] || [ $1 != '-run-tests' ]; then
    exit
fi

if [ ! -f "$TEST_ZIP" ]; then
    echo "Downloading Lua"
    wget https://www.lua.org/tests/lua-5.4.4-tests.tar.gz
fi

echo "Making Lua"
cd $LUA_DIR
make
cd ..

echo "Unzipping Lua tests"
tar -xvf $TEST_ZIP

echo "Running Lua tests"
cd $TEST_DIR
../$SRC_DIR/lua -e"_U=true" all.lua 1>/dev/null

