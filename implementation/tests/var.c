// test transforming macros that expand to variables

#include <stdio.h>

#define ID(x) x

int y = 1;

int main()
{
    int x = 2;

    printf("%d\n",
        // Should transform
        ID(x)
    );

    printf("%d\n",
        // Should transform
        ID(y)
    );

    return 0;
}
