#define ONE 1

struct Foo
{
    // Should not be transformed
    int data : ONE;
};

union Bar
{
    // Should not be transformed
    int data : ONE;
};

int x = ONE;

int main(void)
{
    switch (42)
    {
    // Should not be transformed
    case ONE:
        // Should be transformed
        ONE;
        break;

    case 42:
        switch (77)
        {
        // Should not be transformed
        case ONE:
            break;

        default:
            break;
        }

    default:
        break;
    }

    // Should not be transformed
    int arr[ONE];

    return 0;
}
