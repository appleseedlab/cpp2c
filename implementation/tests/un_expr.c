#define UN_EXPR_PLUS +1
#define UN_EXPR_MINUS -1

int main()
{
    // Should transform
    UN_EXPR_PLUS;

    // Should transform
    UN_EXPR_MINUS;

    return 0;
}
