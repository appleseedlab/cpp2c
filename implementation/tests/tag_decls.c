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

M f(M m) { return m; }
#define CALL_F_WITH(N) f(N)

int main(int argc, char const *argv[])
{
    S s;
    // should be transformed
    GET_X_STATIC(s);
    // should be transformed
    GET_X_STATIC(s);
    // should be transformed
    GET_X_PTR((&s));

    union U u;
    // should be transformed
    GET_X_STATIC(u);
    // should be transformed
    GET_S_STATIC(u);

    M m;
    // should not be transformed
    CALL_F_WITH(m);

    struct T t;
    // should not be transformed
    GET_S_STATIC(t.u);

#undef GET_X_PTR
#define GET_X_PTR(su) su->x
    // should be transformed
    GET_X_PTR((&s));
    return 0;
}
