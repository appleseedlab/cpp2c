struct S {
    #include "two.h"
    int x : TWO;
};

union U {
    #include "four.h"
    int x : FOUR;
};

enum E {
    #include "eight.h"
    A = EIGHT,
};

int main(int argc, char **argv)
{
    // should not transform because decl location is invalid
    TWO;
    // should not transform because decl location is invalid
    FOUR;
    // should not transform because decl location is invalid
    EIGHT;
}