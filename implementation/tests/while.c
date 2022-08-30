// tests transforming macros expanded in while loops

#include <stdio.h>

#define ZERO 0
#define ONE 1

int main()
{
    int i = 0;
    while (
        i <=
        // Should transform
        ZERO
    )
    {
        printf("%d\n",
            // Should transform
            ONE
        );
        i++;
    }

    return 0;
}
