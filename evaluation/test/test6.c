#define S(a) a
#define E(b) b
#define U(c) c

// should be deanonymized to the name s
typedef struct {
    int x;
} s;

typedef s t;

// should be deanonymized to the name u
typedef union {
    int x;
} u;

typedef u v;

// should be deanonymized to the name e
typedef enum {
    X
} e;

typedef e f;

int main(int argc, char **argv) {
    t a;
    v b;
    f c;

    // 1 unique invocation
    // should transform
    S(a);

    // 1 unique invocation
    // should transform
    E(b);

    // 1 unique invocation
    // should transform
    U(c);

    return 0;
}