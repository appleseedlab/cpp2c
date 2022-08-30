// This file demonstrates how transforming expressions
// that contain conditional evaluation may produce
// programs that contain undefined behavior.

#define A_THEN_B(a, b) ((a) && (b))

#define NOT_A_OR_B(a, b) ((!a) || (b))

#define TERN_Z(a, b) ((a) ? (b) : 0)

int main(int argc, char const *argv[])
{
    // p is initialized to NULL
    int *p = ((void *)0);
    // The following 3 macro invocations will not result in
    // undefined behavior because macros are call-by-name.
    // If we transform them to function calls, though, then
    // we they will result in undefined behavior.

    // Should not transform
    int and = A_THEN_B(p, *p);
    // Should not transform
    int or = NOT_A_OR_B(p, *p);
    // Should not transform
    int tern = TERN_Z(p, *p);
    return 0;
}
