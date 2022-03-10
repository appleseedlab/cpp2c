#define X x

int main()
{
    int x;
    x;

    // Should not transform
    X;

    return 0;
}
