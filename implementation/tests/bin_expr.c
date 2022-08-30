// tests macros that involve binary expressions

#include <stdio.h>

#define BIN_EXPR_PLUS 1 + 1
#define BIN_EXPR_MINUS 1 - 1
#define BIN_EXPR_MULT 1 * 1
#define BIN_EXPR_DIV 1 / 1

#define M 1 +
#define N 1

int main()
{
    printf(
        "%d\n",
        // Should transform
        BIN_EXPR_PLUS
    );

    printf(
        "%d\n",
        // Should transform
        BIN_EXPR_MINUS
    );

    printf(
        "%d\n",
        // Should transform
        BIN_EXPR_MULT
    );

    printf(
        "%d\n",
        // Should transform
        BIN_EXPR_DIV
    );

    printf(
        "%d\n",
        // Should not transform
        M
        // Should transform
        N
    );

    return 0;
}
