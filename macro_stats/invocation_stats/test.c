#include "test.h"

#define ONE 1 //
#define TWO() 2 /* */
#define ADD(a, b) ((a) + (b))

int main(void)
{
    ZERO;
    ONE;
    TWO();
    ADD(1, 2);
    return 0;
}
