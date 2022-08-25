#include <stdio.h>

#define ONE 1

enum
{
    VAR =
        // Should not transform
        ONE
};

struct MyStruct
{
    int field :
        // Should not transform
        ONE
    ;
};

union MyUnion
{
    int field :
        // Should not transform
        ONE
    ;
};

int g =
    // Should not transform
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
        // Should not transform
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
        // Should not transform
        ONE
    ] = { 1 };
    printf("%d\n", a[0]);
    return 0;
}