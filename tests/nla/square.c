#include<stdio.h>
#include<stdlib.h>

void vtrace1( int x, int y) {
}

void vtrace2(int x, int y) {
}

void vtrace3(int x, int y) {
}

// void vtrace4(int x0, int y0, int x1, int y1) {
// }

void vloop(int x, int y) {
  vtrace1(x, y);
  int bnd = 500;
  int counter = 0;

  while (x >= 0) {
    if (counter >= bnd)
      break;
    else
      counter++;
    vtrace2(x, y);

    x = x - y*y;
    y = y + 1;
  }
  if (counter < bnd)
    vtrace3(x, y);
}

void mainQ(int x, int y) {
  vloop(x, y);
}

void main(int argc, char **argv){
  //mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*
  // The original code
  while (x >= 0) {
    x = x + y;
    y = y + 1;
  }
 */

