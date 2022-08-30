// tests transforming macros that are on the right hand side of assignments

#include <stdio.h>

#define ONE 1

int main()
{
    int x =
        // Should transform
        ONE
    ;
    printf("x=%d\n", x);
    return 0;
}
