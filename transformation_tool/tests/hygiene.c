#define ADD_UNHYGIENIC(a, b) a + b
#define ADD_HYGIENIC(a, b) (a + b)

int main()
{
    0 * ADD_HYGIENIC(2, 3);
    0 * ADD_UNHYGIENIC(2, 3);
    return 0;
}
