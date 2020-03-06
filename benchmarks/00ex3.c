#include<stdio.h>
#include <stdlib.h>

void foo(int x, int y) {
  int b = x;
  int z = -1 * y;

  while (x >= 0) {
    x = x + z;
    z = z + 1;
  }


  while (b > x) {
    b --;
  }

}

void main(int argc, char **argv){
  foo(atoi(argv[1]), atoi(argv[2]));
}
