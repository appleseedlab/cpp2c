#include <stdio.h>

#define ONE 1
#define TWO 2
#define THREE 3
#define ID(x) (x)

// this comment is one-line
int foo() {
    return
    // Should transform
    ONE
    ;
}

// this comment spans
// multiple
// lines
int bar() {
    return
    // Should transform
    TWO
    ;
}

/* this comment is one-line, but could be more */
int buzz() {
    return
    // Should transform
    THREE
    ;
}

/* this function
spans a few lines
and is made to do so */
int baz() {
    return
    // Should transform
    ID(4)
    ;
}

// this is the main function
int main(int argc, char **argv)
{
    return 0;
}