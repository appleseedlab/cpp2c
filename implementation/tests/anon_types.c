// tests not transforming macros whose transformed signatures contain
// anonymous types

#include <stdio.h>

typedef struct S
{
    int x;
} S;

// Any macros containing
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

M f(M m) { return m; }

#define GET_S_STATIC(u) u.s
#define GET_S_PTR(u) u->s
#define GET_X_PTR(su) su->x
#define CALL_F_WITH(N) f(N)

int main(int argc, char const *argv[])
{
    M m = Y;
    // Should not transform
    printf("%d\n",
        // Should not transform
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

    return 0;
}
