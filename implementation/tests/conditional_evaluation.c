#define A_THEN_B(a, b) ((a) && (b))

#define NOT_A_OR_B(a, b) ((!a) || (b))

#define TERN(a, b) ((a) ? (b) : 0)

int main(int argc, char const *argv[])
{
    int *p = ((void *)0);
    int and = A_THEN_B(p, *p);
    int or = NOT_A_OR_B(p, *p);
    int tern = TERN(p, *p);
    return 0;
}
