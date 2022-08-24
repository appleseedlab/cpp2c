#!/bin/bash

# TODO: figure out how to use ctest for testing

# Assumptions
# - cpp2c has already been made

# delete copied files
rm -f implementation/tests/*.cpy.*

# copy headers
for F in $(ls implementation/tests/*.h)
do
    cp $F $F.cpy.h
done

let ok=0
let fail=0
let i=1
C_FILES=$(ls implementation/tests/*.c)
for F in $C_FILES
do
    F_CPY=$F.cpy.c
    # copy src file
    cp $F $F_CPY

    # include copied headers instead
    # this is to prevent rewriting original headers
    sed -i 's/\.h"/\.h\.cpy\.h"/' $F_CPY

    # transform copied src file
    ./implementation/build/bin/cpp2c tr -i $F_CPY 2>/dev/null

    # compile the src file
    cc $F
    
    # run it and save its output
    ./a.out >original.txt

    # compile the transformed file
    cc -Wno-attributes $F_CPY

    # check that it compiled successfully
    if [ $? -ne 0 ]
    then
        echo "test $i: $(basename $F) fail"
        let fail++
        let i++
        continue
    fi

    # run it and save its output
    ./a.out >transformed.txt
    if [ $? -ne 0 ]
    then
        echo "test $i: $(basename $F) fail"
        let fail++
        let i++
        continue
    fi

    # compare the original and transformed files
    RES=$(cmp original.txt transformed.txt)

    if [ $? -ne 0 ]
    then
        echo "test $i: $(basename $F) fail"
        let fail++
        let i++
        continue
    fi

    echo "test $i: $(basename $F) ok"
    let ok++
    let i++
done

let i--
echo "passing $ok / $i tests"

# delete copied files
rm -f implementation/tests/*.cpy.*

#delete out file
rm -f a.out

# delete test result files
rm -f original.txt transformed.txt