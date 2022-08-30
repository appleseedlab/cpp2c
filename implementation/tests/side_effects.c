// tests transforming macros with side-effects

#include <stdio.h>

#define CALL f(1)
#define ASSIGN_X x = 1
#define SET_Z(x) ((x) = (0))

int x = 0;
int f(int x) { return x; }

int main(void)
{
    printf("%d\n",
        // Should transform
        CALL
    );
    printf("%d\n",
        // Should transform
        ASSIGN_X
    );

    int y = 1;
    printf("%d\n",
        // Should not transform
        SET_Z(y)
    );
    return 0;
}
