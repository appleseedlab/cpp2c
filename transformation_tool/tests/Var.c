#define ID(x) x

int y;

int main()
{
    int x;

    // Should not transform
    ID(x);

    // Should transform
    ID(y);

    return 0;
}
