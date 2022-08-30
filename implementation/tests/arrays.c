// tests transforming macros that contain array types in their signatures

#include <stdio.h>

#define FST(a) a[0]
#define FST_PTR(a) (*a)[0]

int main(int argc, char **argv)
{
    int a[3] = {1, 2, 3};
    int _;
    _ =
        // Should transform
        FST(a);

    _ =
        // Should transform
        FST_PTR((&(a)));

    for (int i=0; i < 3; i++)
        printf("%d ", a[i]);
    printf("\n");

    return 0;
}