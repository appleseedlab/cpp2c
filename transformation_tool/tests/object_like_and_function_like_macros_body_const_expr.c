#define ONE 1
#define THREE() 1 + 2

int main(void)
{
    THREE();
    // Right now THREE() is not transformed, but should it be?
    // If we change the definition of THREE() to (1 + 2), then this
    // invocation will be transformed
    ONE + THREE();
    return 0;
}
