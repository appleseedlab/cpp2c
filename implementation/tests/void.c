// tests transforming macros that contain an argument that is void

#define VOID(v) v

void foo() {}

int main(int argc, char **argv)
{
    // Should not transform
    VOID(foo());
    return 0;
}