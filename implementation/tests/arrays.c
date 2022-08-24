#include <stdio.h>

#define FST(a) a[0]
#define FST_PTR(a) (*a)[0]

int main(int argc, char **argv)
{
    int a[3] = {1, 2, 3};
    int _;
    // should not transform
    _ = FST(a);

    // should not transform
    _ = FST_PTR((&a));

    for (int i=0; i < 3; i++)
        printf("%d ", a[i]);
    printf("\n");

    return _;
}