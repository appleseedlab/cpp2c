#include <stdio.h>

#define sq(x) x * x

int sq_f_wrong(int x) { return x * x; }

int sq_f(int (*y_expr)(int *), int *y) { return (*y_expr)(y) * (*y_expr)(y); }

int y_plus_plus(int *y) { return (*y)++; }

int main() {
  int y;

  y = 2;
  printf("%d\n", sq(y++));

  y = 2;
  printf("%d\n", sq_f_wrong(y++));

  y = 2;
  printf("%d\n", sq_f(&y_plus_plus, &y));
}
