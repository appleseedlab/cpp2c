#define FOO 1 + 2 + 3

#define ADD_UNHYGIENIC(a, b) a + b
#define ADD_HYGIENIC(a, b) (a + b)

#define M 0 + 5
#define N 1 +

#define OUTER INNER

#define INNER 1

int main()
{

    FOO;

    // Should transform
    0 * ADD_HYGIENIC(2, 3);

    // Should not transform
    0 * ADD_UNHYGIENIC(2, 3);

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
