#define ONE 1
#define FOO 1 + 2
#define BAR ONE + FOO
#define BAZ FOO
#define BUZZ 1 + ONE

#define GT_FOO(x) x > FOO

int main()
{
    // Should transform
    ONE;

    // Should transform
    FOO;

    // Should transform
    BAR;

    // Should transform
    BAZ;

    // Should transform
    BUZZ;

    // Should transform
    GT_FOO(3);

    return 0;
}
