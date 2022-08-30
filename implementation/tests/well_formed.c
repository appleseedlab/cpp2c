// tests transforming macros that are syntactically wellformed

#include <stdio.h>

#define FOO 1 + 2 + 3

#define ADD_UNHYGIENIC(a, b) a + b
#define ADD_HYGIENIC(a, b) (a + b)

#define DOUBLE(x) x + x

#define OUTER INNER
#define INNER 1

#define M 0 + 5

#define ADD_THREE(a, b, c) a + b + c

#define ADD_ONE(x) x + 1

#define MULT_ONE(x) x * 1

#define DIV(a, b) a / b

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
        // Should transform
        ADD_UNHYGIENIC(2, 3)
        + 0
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
        // Should transform
        M
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
        // Should transform
        OUTER
    );

    printf("%d\n",
        // Should transform
        ADD_UNHYGIENIC(1 * 1, 1 * 1)
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
        // Should transform
        DIV(1, 1)
    );

    printf("%d\n",
        // Should transform
        DIV((1 + 2 * 0), (1 * 1))
    );


    int x = 0;
    int y = 1;

    printf("%d\n",
        // Should transform
        DIV(x, y)
    );

    printf("%lf\n",
        // Should transform
        DIV(1.0, 2.0)
    );

    return 0;
}
