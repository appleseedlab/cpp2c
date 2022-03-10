int y;
int x;
#define Y y
#define X() x

int main()
{
    y;

    // Should transform
    Y;

    // Should transform
    X();

    return 0;
}
