#define ONE 1
#define THREE() 1 + 2

int main(void)
{
    THREE();
    // Right now THREE() is not transformed, but should it be?
    ONE + THREE();
    return 0;
}
