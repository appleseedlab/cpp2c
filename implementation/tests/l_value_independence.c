// tests transforming macros that involve the & operator but are still
// l-value independent

#define ID(x) x

int x = 0;

int main(int argc, char **argv)
{
    int y = 0;
    // Should transform
    ID(&x);
    // Should transform
    ID(&y);

    return 0;
}