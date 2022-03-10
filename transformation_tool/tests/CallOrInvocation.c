#define ONE 1

#define TWO 1 + 1

int foo(int x) { return x; }

int baz(int x, int y) { return x + y; }

int main()
{
    // Should transform argument
    foo(ONE);

    // Should transform first argument
    bar(ONE, 2);

    // Should transform second argument
    bar(1, TWO);

    // Should transform both argument
    baz(ONE, TWO);

    return 0;
}
