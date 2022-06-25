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

// This should be made not anonymous
typedef enum
{
    Y = 0
} M;

M f(M m) { return m; }
#define CALL_F_WITH(N) f(N)

int main(int argc, char const *argv[])
{
    S s;
    GET_X_STATIC(s);
    GET_X_STATIC(s);
    GET_X_PTR((&s));

    union U u;
    GET_X_STATIC(u);
    GET_S_STATIC(u);

    M m;
    CALL_F_WITH(m);

#undef GET_X_PTR
#define GET_X_PTR(su) su->x
    GET_X_PTR((&s));
    return 0;
}
