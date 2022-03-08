#define BIN_EXPR_PLUS 1 + 1
#define BIN_EXPR_MINUS 1 - 1
#define BIN_EXPR_MULT 1 * 1
#define BIN_EXPR_DIV 1 / 1

#define M 1 +
#define N 1

int main()
{
    // Should transform
    BIN_EXPR_PLUS;
    // Should transform
    BIN_EXPR_MINUS;
    // Should transform
    BIN_EXPR_MULT;
    // Should transform
    BIN_EXPR_DIV;

    // Should not transform M, should transform N
    M N;

    return 0;
}
