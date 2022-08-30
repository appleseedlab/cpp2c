// tests transforming macros that involve string literals

#include <stdio.h>

void println(char *s) { printf("%s\n", s); }

#define PRINT_LN(s) (println(s))

int main(int argc, char **argv)
{
    // Should transform
    PRINT_LN("Hello, World!");

    return 0;
}