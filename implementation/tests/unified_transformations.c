#include <stdio.h>

#define NUM_DAYS_IN_WEEK 7
#define LUCKY_NUMBER 7

#define DOUBLE(x) x * 2
#define SHL1(x) x * 2

int main(int argc, char const *argv[])
{
    // If the -u flag was passed, then these expansions should be transformed
    // to the same transformation.
    // If not, then they should be transformed to separate definitions

    printf("%d\n",
        // Should transform
        NUM_DAYS_IN_WEEK
    );
    
    printf("%d\n",
        // Should transform
        LUCKY_NUMBER
    );

    printf("%d\n",
        // Should transform
        DOUBLE(1)
    );

    printf("%d\n",
        // Should transform
        SHL1(1)
    );

    return 0;
}
