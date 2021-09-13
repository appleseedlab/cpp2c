// Macro    |   Expected Type
#define A 1               // int
#define B 1               // int
#define C 1               // int
#define D 1.0             // double
#define E 1.0             // double
#define F 1.0             // double
#define G 'G'             // char
#define H "Hello, World!" // string
#define I '\n'            // char
#define J "This"   \
          " is"    \
          " a"     \
          " multi" \
          " -line"  \
          " string"
#define K   1\
            2
#define L "This // has // comment // starters // in // it"
#define M "This // has // comment // starters // in // it" // and a comment
#define N "This // has // comment //" \
          "starters // in // it// across // multiple // lines" // and a comment
#define O "Multiple strings" /*comment*/ " with comments" /*comment*/ " between them"
#define P "Multiple strings" /*comment*/ " " \
          "with comments and lines" /*comment*/ " between them"