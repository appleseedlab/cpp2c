#define GET_X_STATIC(su) su.x
#define GET_X_PTR(su) su->x

struct S
{
    int x;
};

union U
{
    int x;
    int y;
};

struct __attribute__((annotate("CPP2C"))) X;

int x __attribute__((annotate("CPP2C")));

int f() __attribute__((annotate("CPP2C")));

int main(int argc, char const *argv[])
{
    struct S s;
    union U u;
    GET_X_STATIC(s);
    GET_X_STATIC(u);
    GET_X_PTR((&s));
#undef GET_X_PTR
#define GET_X_PTR(su) su->x
    GET_X_PTR((&s));
    return 0;
}
