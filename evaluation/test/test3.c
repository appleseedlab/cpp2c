#define DIGITBIT (1)
#define MASK(B) ((1) << (B))
#define testprop(c, p) ((c) & (p))
#define lisdigit(c) (testprop((c), (MASK(DIGITBIT))))

// 4 unique macro definitions

int main(int argc, char const *argv[])
{
    // 5 unique transformations
    lisdigit(DIGITBIT);

    // 5 unique transformations
    return 0;
}
