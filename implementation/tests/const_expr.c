#define ONE 1

enum
{
    // Should not transform
    VAR = ONE
};

struct MyStruct
{
    // Should not transform
    int field : ONE;
};

union MyUnion
{
    // Should not transform
    int field : ONE;
};

// Should not transform
int g = ONE;

int main(int argc, char const *argv[])
{
    // Should transform
    switch (ONE)
    {
    // Should not transform because this must be a constant expression
    case ONE:
        // Should transform
        ONE;
        break;

    default:
        break;
    }

    // Should not transform
    int a[ONE];
    return 0;
}