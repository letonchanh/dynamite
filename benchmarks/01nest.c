#include<stdio.h>
#include <stdlib.h>

void foo(int x, int y) {
  int b = x;
  int z = -1 * y;

  while (x >= 0) {
    x = x + z;
    while (b < 0) {
      b ++;
    }
    z = z + 1;
  }

}

void main(int argc, char **argv){
  foo(atoi(argv[1]), atoi(argv[2]));
}
