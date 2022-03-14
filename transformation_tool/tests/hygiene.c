#define FOO 1 + 2 + 3

#define ADD_UNHYGIENIC(a, b) a + b
#define ADD_HYGIENIC(a, b) (a + b)

#define DOUBLE(x) x + x

#define SQUARE(x) x * x

#define UNUSED_ARG(x) 1

#define M 0 + 5
#define N 1 +

#define OUTER INNER

#define INNER 1

int main()
{
    // Should transform
    FOO;

    // Should transform
    0 * ADD_HYGIENIC(2, 3);

    // Should not transform
    0 * ADD_UNHYGIENIC(2, 3);

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

    // Should not transform
    OUTER;
    // 1

    return 0;
}
