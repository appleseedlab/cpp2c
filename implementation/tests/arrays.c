#define FST(a) a[0]
#define FST_PTR(a) (*a)[0]

int main(int argc, char **argv)
{
    int a[3];
    int _;
    // should not transform
    _ = FST(a);

    // should not transform
    _ = FST_PTR((&a));

    return _;
}