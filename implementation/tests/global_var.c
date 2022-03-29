#include "global_var.h"

int x;
int y;
int z = 1;

#define W w
#define X() x
#define Y y
#define Z z

int main()
{
    // Should transform, and definition should be in this file
    U;

    // Should transform, and definition should be in this file
    W;

    // Should transform
    X();

    // Should transform
    Y;

    // Should transform
    Z;
    return 0;
}
