#include <stdio.h>

#define ONE 1

int main()
{
    printf("%d\n",
        // Should transform
        ONE
    );
    printf("%d\n",
        // Should transform
        ONE
    );

    return 0;
}
