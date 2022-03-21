#define ID(x) x

#define ADD_ONE(x) x + 1

int x = 0;

int foo() { return 0; }

int main()
{
    // Should transform
    ID(1);

    // Should transform
    ID(x);

    // Should transform
    ID((1));

    // Should transform
    ID(-1);

    // Should transform
    ID(1 + 1);

    // Should not transform
    ID(x = 2);

    // Should not transform
    ID(foo());

    // Should transform
    ADD_ONE(1);

    return 0;
}
