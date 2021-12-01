#include <stdio.h>

#define sq(x) x * x

int sq_f(int x) { return x * x; }

int main() {
  printf("%d\n", sq(2));
  printf("%d\n", sq_f(2));
}
