#define VAR_M(...) __VA_ARGS__

int add(int x, int y) { return x + y; }

int main(int argc, char const *argv[])
{
    // should not transform
    // 1 unique invocation
    add(VAR_M(1, 2));

    // should not transform
    // 1 unique invocation
    VAR_M(1, 2);
    return 0;
}
