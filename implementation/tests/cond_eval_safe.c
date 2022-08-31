// This file demonstrates how sometimes we can transform macros
// involving conditional evaluation without introducing undefined
// behavior.

#define A_THEN_B(a, b) ((a) && (b))

#define NOT_A_OR_B(a, b) ((!a) || (b))

#define TERN_Z(a, b) ((a) ? (b) : 0)

int main(int argc, char const *argv[])
{

    // Some conditional evaluation macros are indeed safe to transform though.
    // In the future, it would be nice if we could identify and transform
    // such macros.
    // For example:
    // Should transform
    A_THEN_B(1, 2);
    // Should transform
    NOT_A_OR_B(0, 1);
    // Should transform
    TERN_Z(0, 1);
    return 0;
}
