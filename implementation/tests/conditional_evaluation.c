#include <stdlib.h>
#include <stdio.h>

#define AND(a, b) ((a) ? (b) : 0)

int main(int argc, char const *argv[])
{
    int *p = NULL;
    int r = AND(p, *p);
    return 0;
}
