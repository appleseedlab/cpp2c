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

// Any transformed definitions containing
// anonymous types should not be transformed
typedef enum
{
    Y = 0
} M;

struct T {
    union {
        S s;
    } u;
};

#define GET_S_PTR(u) u->s

M f(M m) { return m; }
#define CALL_F_WITH(N) f(N)

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

    M m = Y;
    // Should not transform
    printf("%d\n",
        // Should transform
        CALL_F_WITH(m)
    );

    struct T t;
    t.u.s.x = 1;
    printf("%d\n",
        // Should not transform
       GET_S_STATIC(t.u)
       .x
    );

    printf("%d\n",
        // Should not transform
       GET_S_PTR((&(t.u)))
       .x
    );

#undef GET_X_PTR
#define GET_X_PTR(su) su->x

    printf("%d\n",
        // Should not transform
       GET_X_PTR((&(s)))
    );
    return 0;
}
