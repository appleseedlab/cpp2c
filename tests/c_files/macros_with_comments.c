#define A 1                // int
#define B 'C'              // char
#define C "String literal" // string
#define D 2.0              // float / double
#define E "A B C " \
          "D E F" // multi-line string
#define F "This"   \
          " is"    \
          " a"     \
          " multi" \
          "-line"  \
          " string"
#define G   1\
            2
#define H "This // has // comment // starters // in // it"
#define I "This // has // comment // starters // in // it" // and a comment
#define J "This // has // comment // " \
          "starters // in // it // across // multiple // lines" // and a comment
#define K "Multiple strings" /*comment*/ " with comments" /*comment*/ " between them"
#define L "Multiple strings" /*comment*/ " " \
          "with comments and lines" /*comment*/ " between them"