#include <stdio.h>

#define INNER 1
#define OUTER1 INNER
#define OUTER2 INNER
#define SINGLE_DOUBLE_QUOTE "
#define DOUBLE_DOUBLE_QUOTE ""
#define DOUBLE_DOUBLE_QUOTE_WITH_NEWLINE "\
"

#define COMMA ,

#define COMMAS , , , , , ", , " \, ','
#define COMMAS_BAD , , , , , ", , \, ',

int main()
{
    // We should report that INNER was expanded at 3 unique spelling locations
    INNER;
    OUTER1;
    OUTER1;
    OUTER2;
    OUTER2;
}