int y;
int x;
#define Y y
#define X() x

int main()
{
    y;
    Y;
    X();
    return 0;
}
