#!/bin/bash

# TODO: figure out how to use ctest for testing

# Assumptions
# - cpp2c has already been made

# Reads the file line-by-line, and if a line contains
# the search string, echoes out the following line
function echo_lines_after_text {
    P_LINE=false
    NEEDLE="$1"
    while read line
    do
        if $P_LINE; then
            echo "$line"
            P_LINE=false
        fi

        if echo "$line" | grep -q "$NEEDLE"; then
            P_LINE=true
        fi
    done < "$2"
}

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
C_FILES=""

if [ $# != 0 ]
then
    # if the user passed specific tests, only run those tests
    C_FILES="$@"
else
    # otherwise, run all tests
    C_FILES=$(ls implementation/tests/*.c)
fi

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

    # Check that every invocation that should have been transformed was
    # transformed
    ORIGINAL=$(echo_lines_after_text "Should transform" "$F")
    TRANSFORMED=$(echo_lines_after_text "Should transform" "$F_CPY")
    IFS=$'\n' read -d '' -a o_lines < <(echo "$ORIGINAL")
    IFS=$'\n' read -d '' -a t_lines < <(echo "$TRANSFORMED")
    LEN=${#o_lines[@]}

    FAILED=false
    for (( j = 0 ; j < $LEN ; j++ ))
    do
        if [ "${o_lines[$j]}" == "${t_lines[$j]}" ]
        then
            echo "Not transformed: ${o_lines[$j]}"
            FAILED=true
        fi
    done
    if $FAILED
    then
        echo "test $i: $(basename $F) fail"
        let fail++
        let i++
        continue
    fi

    # Check that every invocation that should not have been transformed
    # was not transformed
    ORIGINAL=$(echo_lines_after_text "Should not transform" "$F")
    TRANSFORMED=$(echo_lines_after_text "Should not transform" "$F_CPY")
    if ! diff <(echo "$ORIGINAL") <(echo "$TRANSFORMED")
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
echo "passed $ok / $i tests"

# delete copied files
rm -f implementation/tests/*.cpy.*

#delete out file
rm -f a.out

# delete test result files
rm -f original.txt transformed.txt