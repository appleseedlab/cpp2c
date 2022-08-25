#include <stdio.h>

#define UN_EXPR_PLUS +1
#define UN_EXPR_MINUS -1

int main()
{
    printf("%d\n",
        // Should transform
        UN_EXPR_PLUS
    );

    printf("%d\n",
        // Should transform
        UN_EXPR_MINUS
    );

    return 0;
}
