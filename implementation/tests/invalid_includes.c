// tests transforming macros who are declared in a header #include'd at
// an invalid location

#include <stdio.h>

struct S {
    #include "two.h"
    int x : TWO;
};

union U {
    #include "four.h"
    int x : FOUR;
};

enum E {
    #include "eight.h"
    A = EIGHT,
};

int sixteen() {
    #include "sixteen.h"
    return SIXTEEN;
}

int main(int argc, char **argv)
{
    
    printf("%d\n",
        // Should not transform
        TWO
    );

    printf("%d\n",
        // Should not transform
        FOUR
    );

    printf("%d\n",
        // Should not transform
        EIGHT
    );

    printf("%d\n",
        // Should not transform
        SIXTEEN
    );

    return 0;
}