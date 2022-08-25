#include <stdio.h>

#define CALL f(1)
#define ASSIGN_X x = 1

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
    return 0;
}
