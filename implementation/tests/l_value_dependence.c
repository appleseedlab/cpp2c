// tests not transforming macros involving the & operator that are l-value
// dependent

#define ADDR(x) (&(x))

int x = 0;

int main(int argc, char **argv)
{
    int y = 0;

    // Should not transform
    ADDR(x);
    // Should not transform
    ADDR(y);

    return 0;
}