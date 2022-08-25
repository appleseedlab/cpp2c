#include <stdio.h>

#define X x
int y = 0;
#define Y y

int main()
{
    int x = 1;
    x;

    printf("%d\n",
        // Should not transform
        X
    );
    ;

    y;

    printf("%d\n",
        // Should transform
        Y
    );
    ;

    return 0;
}
