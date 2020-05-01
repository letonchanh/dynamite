#include<stdio.h>
#include <stdlib.h>

void vtrace1( int x, int y) {
}

void vtrace2(int x, int y) {
}

void vtrace3(int x, int y) {
}

// void vtrace4(int x0, int y0, int x1, int y1) {
// }

void vloop(int* PTR_x, int* PTR_y) {
  int x = *PTR_x;
  int y = *PTR_y;
  // Analyze loop under pre-conditions inferred from random inputs
  vtrace1(x, y);
  int bnd = 500;
  int counter = 0;

  while (x >= 0) {
    if (counter >= bnd)
      break;
    else
      counter++;
    vtrace2(x, y);

    // int x0 = x;
    // int y0 = y;

    x = x + y;
    y = y + 1;

    // int x1 = x;
    // int y1 = y;
    // vtrace4(x0, y0, x1, y1);
  }
  if (counter < bnd)
    vtrace3(x, y);

  *PTR_x = x;
  *PTR_y = y;
}

void mainQ(int x, int y) {
  // Run mainQ with random inputs to get pre-conditions of vloop
  //if (y >= 1)
    vloop(&x, &y);
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*
  // The original code
  while (x >= 0) {
    x = x + y;
    y = y + 1;
  }
 */

