#include "header.h"

int main(int argc, char const *argv[])
{
    // 1 unique transformed expansion
    // (If transformed after test1.c;
    // otherwise this would have 2 and test.c's
    // expansions of this macro would each have 1)
    PLUS_ONE(1);

    // 1 unique transformation
    // (or 2, see above)
    X_PLUS_Y(2.0, 1);

    // 1 unique transformation
    X_TIMES_2(2.0);

    // 3 unique transformed expansion total
    return 0;
}
