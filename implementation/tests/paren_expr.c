#include <stdio.h>

#define PAREN_EXPR (1)

int main()
{
    printf("%d\n",
        // Should transform
        PAREN_EXPR
    );

    return 0;
}
