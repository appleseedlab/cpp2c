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

int main()
{
    // Should transform
    FOO;

    // Should transform
    0 * ADD_HYGIENIC(2, 3);

    // Should transform
    ADD_HYGIENIC(2, 3) * 0;

    // Should not transform
    0 * ADD_UNHYGIENIC(2, 3);

    // Should not transform
    ADD_UNHYGIENIC(2, 3) * 0;

    // Should not transform
    0 + ADD_UNHYGIENIC(2, 3);

    // Should transform
    ADD_UNHYGIENIC(2, 3) + 0;

    // Should not transform
    SQUARE(5 + 0);

    // Should not transform
    DOUBLE(1 + 1);

    // Should transform
    DOUBLE(1);

    // Should transform
    DOUBLE((1 + 1));
    // (1 + 1) + (1 + 1)

    // Should transform
    DOUBLE(1 * 1);

    // Should not transform
    UNUSED_ARG(1);

    // Should transform
    M;

    // Should not transform
    M * 1;

    // Should not transform
    M *M * 1;
    // 0 + 5 * 0 + 5 * 1

    // Should only transform parenthesized expression
    (M) * M * 1;
    // (0 + 5) * 0 + 5 * 1

    // Should only transform parenthesized expression
    M *(M)*1;
    // 0 + 5 * (0 + 5) * 1

    // Should transform both parenthesized expressions
    (M) * (M)*1;
    // (0 + 5) * (0 + 5) * 1

    // Should not transform
    N N 1;
    // 1 + 1 + 1

    // Should transform
    OUTER;
    // 1

    // Should transform
    ADD_UNHYGIENIC(1 * 1, 1 * 1);

    // Should not transform
    MULT_UNHYGIENIC(0 + 5, 0 + 5);

    // Should transform
    ADD_THREE(1, 1, 1);

    // Should transform
    ADD_THREE(1 * 0, 1 * 0, 1 * 0);

    // Should not transform
    ADD_THREE(1 + 0, 1 + 0, 1 + 0);

    // Should transform
    ADD_ONE(0 * 5);

    // Should transform (see Clang parse tree for explanation)
    ADD_ONE(0 + 5);

    // Should transform
    MULT_ONE(0 * 5);

    // Should not transform
    MULT_ONE(0 + 5);

    // Should not transform
    DIV(25, 3 + 2);

    // Should transform
    DIV(1, 1);

    // Should transform
    DIV((1 + 2 * 0), (1 * 1));

    // Should not transform
    PREFIX_WITH_10();

    // Should not transform
    PREFIX_WITH_10(1);

    int x = 0;
    int y = 1;

    // Should transform
    DIV(x, y);

    // Should transform
    DIV(1.0, 2.0);

    // Should not transform
    ADDR(x);

    return 0;
}
