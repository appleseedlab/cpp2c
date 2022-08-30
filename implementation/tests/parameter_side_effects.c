// tests not transforming macros with parameter side-effects

#include <stdio.h>
#include <stdlib.h>

#define SET_TO_ZERO(x) ((x) = (0))
#define SET_INDEX_1_TO_0(xs) ((xs[1]) = (0))
#define SET_INDEX_1_TO_0_ARITH(xs) ((*(xs + 1)) = (0))

#define ID(x) x

int g = 0;

void print_list(int *xs, int n) { for (int i = 0; i < n; i++) printf("%d ", xs[i]); printf("\n"); }


int main(void)
{
    int x = 1;
    // Side effects on arg in body (passed local var)
    printf("%d\n",
        // Should not transform
        SET_TO_ZERO(x)
    );
    // Side effects on arg in body (passed global var)
    printf("%d\n",
        // Should not transform
        SET_TO_ZERO(g)
    );

    // Side effects on arg in arg list (passed local var)
    printf("%d\n",
        // Should not transform
        ID(x = 1)
    );
    // Side effects on arg in arg list (passed global var)
    printf("%d\n",
        // Should not transform
        ID(g = 2)
    );

    int *xs = (int*) malloc(sizeof(int) * 2);
    xs[0] = 1;
    xs[1] = 2;

    // Side effects on arg in body, but not directly
    printf("%d\n",
        // Should not transform
        SET_INDEX_1_TO_0(xs)
    );
    print_list(xs, 2);

    xs[1] = 2;
    // Side effects on arg in body, but not directly
    printf("%d\n",
        // Should not transform
        SET_INDEX_1_TO_0_ARITH(xs)
    );
    print_list(xs, 2);

    // TODO: once we get array types working, call the last two tests again with
    // a global array

    free(xs);

    return 0;
}
