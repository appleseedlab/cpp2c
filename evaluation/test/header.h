#define ONE 1
#define PLUS_ONE(z) ((z) + ONE)
#define ID(x) (x)
#define X_PLUS_Y(x, y) ((x) + ID(y))
#define X_TIMES_2(x) ((x)*2)

#define L1(x, y) ((x) + (y))
#define L2(x, y) ((L1(x, y)) + (L1(y, x)))
