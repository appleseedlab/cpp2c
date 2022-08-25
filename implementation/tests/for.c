#include <stdio.h>

#define ONE 1

int main(void)
{

    for (int i =
        // Should transform
        ONE
        ; i <=
        // Should transform
        ONE
        ; i +=
        // Should transform
        ONE
        )
    {
        printf(
            "%d\n",
            // Should transform
            ONE
        );
    }

    int j = 0;
    for (j =
        // Should transform
        ONE
        ; j <=
        // Should transform
        ONE
        ; j +=
        // Should transform
        ONE
        )
    {
        printf(
            "%d\n",
            // Should transform
            ONE
        );
    }

    return 0;
}
