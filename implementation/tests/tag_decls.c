// tests transforming macros whose transformed signatures contain tag decls
// (structs/unions/enums)

#include <stdio.h>

#define GET_X_STATIC(su) su.x
#define GET_X_PTR(su) su->x
#define GET_S_STATIC(u) u.s

typedef struct S
{
    int x;
} S;

union U
{
    int x;
    int y;
    S s;
};


int main(int argc, char const *argv[])
{
    S s;
    s.x = 1;
    printf("%d\n",
        // Should transform
        GET_X_STATIC(s)
    );
    printf("%d\n",
        // Should transform
        GET_X_STATIC(s)
    );
    printf("%d\n",
        // Should transform
        GET_X_PTR((&(s)))
    );

    union U u;
    u.x = 2;
    printf("%d\n",
        // Should transform
        GET_X_STATIC(u)
    );
    printf("%d\n",
        // Should transform
        GET_X_STATIC(u)
    );


#undef GET_X_PTR
#define GET_X_PTR(su) su->x

    printf("%d\n",
        // Should transform
       GET_X_PTR((&(s)))
    );
    return 0;
}
