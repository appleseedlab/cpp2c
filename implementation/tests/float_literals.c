// tests transforming macros that expand to floating-point literals

#include <stdio.h>

#define PI 3.14
#define PI_LONG 3.14159265359

int main()
{
    printf("%f\n",
        // Should transform
        PI
    );

    printf("%lf\n",
        // Should transform
        PI_LONG
    );

    return 0;
}
