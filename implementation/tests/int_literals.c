// tests transforming macros that expand to integer literals

#include <stdio.h>

#define ONE 1

int main()
{
    printf("%d\n",
        // Should transform
        ONE
    );

    return 0;
}
