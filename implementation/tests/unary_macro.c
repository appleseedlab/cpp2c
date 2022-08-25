#include <stdio.h>

#define ID(x) x

#define ADD_ONE(x) x + 1

int x = 0;

int foo() { return 0; }

int main()
{
     printf("%d\n",
        // Should transform
        ID(1)
    );

    printf("%d\n",
        // Should transform
        ID(x)
    );

    printf("%d\n",
        // Should transform
        ID((1))
    );

    printf("%d\n",
        // Should transform
        ID(-1)
    );

    printf("%d\n",
        // Should transform
        ID(1 + 1)
    );

    printf("%d\n",
        // Should not transform
        ID(x = 2)
    );

    printf("%d\n",
        // Should not transform
        ID(foo())
    );

    printf("%d\n",
        // Should transform
        ADD_ONE(1)
    );

    return 0;
}
