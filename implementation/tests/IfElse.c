#define ONE 1

int main()
{
    // Should transform
    if (ONE)
    {
        // Should transform
        ONE;
    }

    // Should transform
    if (ONE)
    {
        // Should transform
        ONE;
    }
    else
    {
        // Should transform
        ONE;
    }

    return 0;
}
