// tests transforming macros that are part of expression statements

#include <stdio.h>

int x = 0;

int foo() { return 0; }

#define NUM 1
#define VAR x
#define PAREN_EXPR (1)
#define UN_EXPR -1
#define BIN_EXPR 1 + 1
#define ASSIGN x = 2
#define CALL_OR_INVOCATION foo()

int main()
{
    printf("%d\n",
        // Should transform
        NUM
    );
    printf("%d\n",
        // Should transform
        VAR
    );
    printf("%d\n",
        // Should transform
        PAREN_EXPR
    );
    printf("%d\n",
        // Should transform
        UN_EXPR
    );
    printf("%d\n",
        // Should transform
        BIN_EXPR
    );
    printf("%d\n",
        // Should transform
        ASSIGN
    );
    printf("%d\n",
        // Should transform
        CALL_OR_INVOCATION
    );

    return 0;
}
