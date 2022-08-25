#include <stdio.h>

#define FOO 1 + 2 + 3

#define ADD_UNHYGIENIC(a, b) a + b
#define ADD_HYGIENIC(a, b) (a + b)

#define DOUBLE(x) x + x

#define SQUARE(x) x *x

#define UNUSED_ARG(x) 1

#define M 0 + 5
#define N 1 +

#define OUTER INNER

#define INNER 1

#define MULT_UNHYGIENIC(a, b) a *b

#define ADD_THREE(a, b, c) a + b + c

#define ADD_ONE(x) x + 1

#define MULT_ONE(x) x * 1

#define DIV(a, b) a / b

#define PREFIX_WITH_10(x) 10##x

#define ADDR(x) &x

#define QUOTE " \
        "

int main()
{
    printf("%d\n",
        // Should transform
        FOO
    );

    printf("%d\n",
    0 *
        // Should transform
        ADD_HYGIENIC(2, 3)
    );

    printf("%d\n",
        // Should transform
        ADD_HYGIENIC(2, 3)
            * 0
    );

    printf("%d\n",
    0 *
        // Should not transform
        ADD_UNHYGIENIC(2, 3)
    );

    printf("%d\n",
        // Should not transform
        ADD_UNHYGIENIC(2, 3)
        * 0
    );

    printf("%d\n",
        0 +
            // Should not transform
            ADD_UNHYGIENIC(2, 3)
    );

    printf("%d\n",
        // Should transform
        ADD_UNHYGIENIC(2, 3)
        + 0
    );

    printf("%d\n",
        // Should not transform
        SQUARE(5 + 0)
    );

    printf("%d\n",
        // Should not transform
        SQUARE(2*2)
    );

    printf("%d\n",
        // Should not transform
        DOUBLE(1 + 1)
    );

    printf("%d\n",
        // Should transform
        DOUBLE(1)
    );

    printf("%d\n",
        // Should transform
        DOUBLE((1 + 1))
    );
    // (1 + 1) + (1 + 1)

    printf("%d\n",
        // Should transform
        DOUBLE(1 * 1)
    );

    printf("%d\n",
        // Should not transform
        UNUSED_ARG(1)
    );

    printf("%d\n",
        // Should transform
        M
    );

    printf("%d\n",
        // Should not transform
        M * 1
    );

    printf("%d\n",
        // Should not transform
        M 
        *
        // Should not transform
        M 
        * 1
    );
    // 0 + 5 * 0 + 5 * 1

    printf("%d\n",
        // Should transform
        (M)
        *
        // Should not transform
        M
        * 1
    );
    // (0 + 5) * 0 + 5 * 1

    printf("%d\n",
        // Should not transform
        M
        *
        // Should transform
        (M)
        * 1
    );

    printf("%d\n",
        // Should transform
        (M)
        *
        // Should transform
        (M)
        * 1
    );

    printf("%d\n",
        // Should not transform
        N
        // Should not transform
        N
        1
    );

    printf("%d\n",
        // Should transform
        OUTER
    );

    printf("%d\n",
        // Should transform
        ADD_UNHYGIENIC(1 * 1, 1 * 1)
    );

    printf("%d\n",
        // Should not transform
        MULT_UNHYGIENIC(0 + 5, 0 + 5)
    );

    printf("%d\n",
        // Should transform
        ADD_THREE(1, 1, 1)
    );

    printf("%d\n",
        // Should transform
        ADD_THREE(1 * 0, 1 * 0, 1 * 0)
    );

    printf("%d\n",
        // Should not transform
        ADD_THREE(1 + 0, 1 + 0, 1 + 0)
    );

    printf("%d\n",
        // Should transform
        ADD_ONE(0 * 5)
    );

    printf("%d\n",
        // Should transform
        ADD_ONE(0 + 5)
    );

    printf("%d\n",
        // Should transform
        MULT_ONE(0 * 5)
    );

    printf("%d\n",
        // Should not transform
        MULT_ONE(0 + 5)
    );

    printf("%d\n",
        // Should not transform
        DIV(25, 3 + 2)
    );

    printf("%d\n",
        // Should transform
        DIV(1, 1)
    );

    printf("%d\n",
        // Should transform
        DIV((1 + 2 * 0), (1 * 1))
    );

    printf("%d\n",
        // Should not transform
        PREFIX_WITH_10()
    );

    printf("%d\n",
        // Should not transform
        PREFIX_WITH_10(1)
    );

    int x = 0;
    int y = 1;

    printf("%d\n",
        // Should transform
        DIV(x, y)
    );

    // Should transform
    printf("%lf\n",
        DIV(1.0, 2.0)
    );

    // Should not transform
    ADDR(x);

    return 0;
}
