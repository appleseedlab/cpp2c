#include <stdio.h>

#define ONE 1

enum
{
    VAR =
        // Should transform
        ONE
};

struct MyStruct
{
    int field :
        // Should transform
        ONE
    ;
};

union MyUnion
{
    int field :
        // Should transform
        ONE
    ;
};

int g =
    // Should transform
    ONE
;

int main(int argc, char const *argv[])
{
    switch (
        // Should transform
        ONE
    )
    {
    case
        // Should transform
        ONE
    :
        printf("%d\n",
            // Should transform
            ONE
        );
        break;

    default:
        break;
    }

    int a[
        // Should transform
        ONE
    ] = { 1 };
    printf("%d\n", a[0]);
    return 0;
}