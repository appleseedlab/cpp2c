#include <stdio.h>

#define set(x) y = x + 1

int set_f(int x, int *y) { return (*y) = x + 1; }

int main() {
  int y = 2;
  printf("%d\n", set(3));
  printf("%d\n", set_f(3, &y));
}
