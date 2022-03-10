#define ONE 1
#define FOO 1 + 2
#define BAR ONE + FOO
#define BAZ FOO
#define BUZZ 1 + ONE

int main()
{
    // Should transform
    ONE;

    // Should transform
    FOO;

    // Should not transform
    BAR;

    // Should not transform
    BAZ;

    // Should not transform
    BUZZ;

    return 0;
}
