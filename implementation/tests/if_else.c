// tests transforming macros in if else statements

#include <stdio.h>

#define ONE 1

int main()
{
    if (
        // Should transform
        ONE
    )
    {
        printf("%d\n",
            // Should transform
            ONE
        );
    }

    if (
        // Should transform
        ONE
    )
    {
        printf("%d\n",
            // Should transform
            ONE
        );
    }
    else
    {
        printf("%d\n",
            // Should transform
            ONE
        );
    }

    return 0;
}
