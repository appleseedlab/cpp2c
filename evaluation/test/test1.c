#include "header.h"

int x = 0;

#define INNER (x)
#define MIDDLE ((INNER) + (INNER))
#define OUTER ((MIDDLE) + (MIDDLE) + (MIDDLE))

// 3 unique macro definitions

int main(int argc, char const *argv[])
{
    // 6 unique transformed expansions
    OUTER;
    // 1 unique transformed expansion
    OUTER;

    // 1 unique transformed expansion
    MIDDLE;
    // 1 unique transformed expansion
    MIDDLE;

    // 1 unique transformed expansion
    INNER;
    // 1 unique transformed expansion
    INNER;

    // 2 unique transformed expansions
    PLUS_ONE(1);

    // 1 unique transformed expansion
    PLUS_ONE(1.0);

    // 2 unique transformed expansions
    X_PLUS_Y(1, 2);
    // 1 unique transformed expansion
    X_PLUS_Y(1, 2.0);

    // 3 unique transformed expansions
    L2(1, 2);
    // 1 unique transformed expansion
    L2(1, 2.0);

    // 21 unique transformed expansions total
    return 0;
}
