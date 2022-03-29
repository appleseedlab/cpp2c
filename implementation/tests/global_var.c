int x;
int y;
int z = 1;
#define X() x
#define Y y
#define Z z

int main()
{
    // Should transform
    X();

    // Should transform
    Y;

    // Should transform
    Z;
    return 0;
}
