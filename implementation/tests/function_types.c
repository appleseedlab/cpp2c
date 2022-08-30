// tests transforming macros that contain function types in their signatures

#include <stdio.h>

int f(int x) { return x; }

#define CALL_WITH_0(f) (f(0))

int main(int argc, char **argv)
{
    printf("%d\n",
        // Should transform
        CALL_WITH_0(f)
    );

    return 0;
}