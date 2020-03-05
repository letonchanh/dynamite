#include<stdio.h>
#include <stdlib.h>

void vloop(int x, int y) {
  // INSTRUMENT: vtrace1(x, y);
  // INSTRUMENT: int bnd = 500;
  // INSTRUMENT: int counter = 0;

  while (x >= 0) {
    // INSTRUMENT: if (counter >= bnd)
    // INSTRUMENT:   break;
    // INSTRUMENT: else
    // INSTRUMENT:   counter++;
    // INSTRUMENT: vtrace2(x, y);

    x = x + y;
    y = y + 1;

    // INSTRUMENT: vtrace4(x0, y0, x1, y1);
  }
  // INSTRUMENT: if (counter < bnd)
  // INSTRUMENT:   vtrace3(x, y);
}

void mainQ(int x, int y) {
  // Run mainQ with random inputs to get pre-conditions of vloop
  //if (y >= 0)
  vloop(x, y);
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

