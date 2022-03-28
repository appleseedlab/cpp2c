#define ONE 1

int main(void)
{

    // Should transform all three expressions
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
