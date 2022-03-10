int x = 0;

int foo() { return 0; }

#define NUM 1
#define VAR x
#define PAREN_EXPR (1)
#define UN_EXPR -1
#define BIN_EXPR 1 + 1
#define ASSIGN x = 2
#define CALL_OR_INVOCATION foo()

int main()
{
    // Should transform
    NUM;
    // Should transform
    VAR;
    // Should transform
    PAREN_EXPR;
    // Should transform
    UN_EXPR;
    // Should transform
    BIN_EXPR;
    // Should not transform
    ASSIGN;
    // Should not transform
    CALL_OR_INVOCATION;

    return 0;
}
