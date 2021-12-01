#include <stdio.h>

#define mul(x) x * y

int mul_f(int x, int *y) { return x * (*y); }

int main() {
  int y = 2;
  printf("%d\n", mul(3));
  printf("%d\n", mul_f(3, &y));
}
