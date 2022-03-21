#define ONE_MOD_TWO 1 % 2
#define ONE 1

int main(void)
{
    // Should transform
    ONE_MOD_TWO;

    // Should transform
    switch (ONE)
    {
    // Should not transform
    case ONE:
        // Should transform
        ONE;
        break;

    default:
        break;
    }

    // Should transform cond and inc (not init because it's a declaration)
    for (int i = ONE; i < ONE; i += ONE)
    {
        // Should transform
        ONE;
    }

    // Should transform all three expressions
    int j = 0;
    for (j = ONE; j < ONE; j += ONE)
    {
        // Should transform
        ONE;
    }

    return 0;
}
