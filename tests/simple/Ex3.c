#include<stdio.h>
#include<stdlib.h>

void vtrace1(int x) {
}

void vtrace2(int x) {
}

void vtrace3(int x) {
}

// void vtrace4(int x0, int y0, int x1, int y1) {
// }

void vloop(int x) {
  // Analyze loop under pre-conditions inferred from random inputs
  vtrace1(x);
  int bnd = 10;
  int counter = 0;

  while (x>=0 && x < 15) {
    if (counter >= bnd)
      break;
    else
      counter++;
    vtrace2(x);

    // int x0 = x;
    // int y0 = y;

    x = x + 1;

    // int x1 = x;
    // int y1 = y;
    // vtrace4(x0, y0, x1, y1);
  }
  if (counter < bnd)
    vtrace3(x);
}

void mainQ(int x) {
  // Run mainQ with random inputs to get pre-conditions of vloop
  // if (y >= 0)
    vloop(x);
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

/*
  // The original code
  while (x >= 0) {
    x = x + y;
    y = y + 1;
  }
 */

