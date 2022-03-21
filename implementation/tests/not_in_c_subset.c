#define ONE_MOD_TWO 1 % 2
#define ONE 1

int main(void)
{
    // Should not transform
    ONE_MOD_TWO;

    // Should not transform
    switch (ONE)
    {
    // Should not transform
    case ONE:
        // Should not transform
        ONE;
        break;

    default:
        break;
    }
    return 0;
}
