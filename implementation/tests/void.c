#define VOID(v) v

void foo() {}

int main(int argc, char **argv)
{
    // should not transform
    VOID(foo());
    return 0;
}