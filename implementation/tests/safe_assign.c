// tests transforming macros have side-effects that are safe to transform

#include <stdio.h>

#define ONE 1

#define ID(x) x

#define ADD(a, b) ((a) + (b))

int f(int x) { return x; }

#define CALL_F_WITH_1 f(1)

int g = 0;

#define ASSIGN_G_TO_1 ((g) = (1))
#define ASSIGN_G_TO(x) ((g) = (x))

int main()
{
    int x =
        // Should transform
        ONE
    ;
    printf("x=%d\n", x);
    int y =
        // Should transform
        ID(2)
    ;
    printf("y=%d\n", y);
    int z =
        // Should transform
        ADD(1, 2)
    ;
    printf("z=%d\n", z);

    printf("f(1)=%d\n",
        // Should transform
        CALL_F_WITH_1
    );
    printf("g=%d\n",
        // Should transform
        ASSIGN_G_TO_1
    );
    printf("g=%d\n",
        // Should transform
        ASSIGN_G_TO(2)
    );

    return 0;
}
