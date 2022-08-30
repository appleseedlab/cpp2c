// tests transforming and not transforming macros involving the & operator

#define ID(x) x
#define ADDR(x) (&(x))

int x = 0;

int main(int argc, char **argv)
{
    int y = 0;
    // Should transform
    ID(&x);
    // Should transform
    ID(&y);

    // Should not transform
    ADDR(x);
    // Should not transform
    ADDR(y);

    

    return 0;
}