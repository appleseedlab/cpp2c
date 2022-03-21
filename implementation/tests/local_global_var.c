#define X x
int y;
#define Y y

int main()
{
    int x;
    x;

    // Should not transform
    X;

    y;

    // Should transform
    Y;

    return 0;
}
