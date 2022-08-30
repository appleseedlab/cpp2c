// tests transforming macros that contain nested macros

#include <stdio.h>

#define ONE 1
#define FOO 1 + 2
#define BAR ONE + FOO
#define BAZ FOO
#define BUZZ 1 + ONE

#define GT_FOO(x) x > FOO

int main()
{
    printf("%d\n",
        // Should transform
        ONE
    );

    printf("%d\n",
        // Should transform
        FOO
    );

    printf("%d\n",
        // Should transform
        BAR
    );

    printf("%d\n",
        // Should transform
        BAZ
    );

    printf("%d\n",
        // Should transform
        BUZZ
    );

    printf("%d\n",
        // Should transform
        GT_FOO(3)
    );

    return 0;
}
