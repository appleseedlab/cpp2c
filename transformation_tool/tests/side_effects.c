#define CALL f(1)
#define ASSIGN_X x = 1

int x = 0;
int f(int x) { return x; }

int main(void)
{
    // Should not transform
    CALL;
    // Should not transform
    ASSIGN_X;
    return 0;
}
