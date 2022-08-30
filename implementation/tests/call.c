// tests macros that expand to function arguments.

#define ONE 1

#define TWO 1 + 1

int foo(int x) { return x; }

int bar(int x, int y) { return x + y; }

int baz(int x, int y) { return x * y; }

int main()
{
    foo(
        // Should transform
        ONE
    );

    bar(
        // Should transform
        ONE
        ,
        2
    );

    bar(
        1,
        // Should transform
        TWO
    );

    baz(
        // Should transform
        ONE
        ,
        // Should transform
        TWO
    );

    return 0;
}
