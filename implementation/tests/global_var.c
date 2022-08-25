#include "global_var.h"

#include <stdio.h>

int x = 3;
int y = 4;
int z = 5;

#define W w
#define X() x
#define Y y
#define Z z

int main()
{
    printf(
        "%d\n",
        // Should transform
        U
    );

    printf(
        "%d\n",
        // Should transform
        W
    );

    printf(
        "%d\n",
        // Should transform
        X()
    );

    printf(
        "%d\n",
        // Should transform
        Y
    );

    printf(
        "%d\n",
        // Should transform
        Z
    );
    return 0;
}
