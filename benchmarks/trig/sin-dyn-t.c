#include <math.h>
#include <stdio.h>

void vtrace1(int x, int y, int a) {}
void vtrace2(int x, int y, int a) {}
void vtrace3(int x, int y, int a) {}

void vloop(int x, int y, int a) {
  vtrace1(x,y,a);

  int bnd = 500; int counter = 0;

  while (y + a < 42) {
    if (counter >= bnd)
      break;
    else
      counter++;
    vtrace2(x,y,a);

    int t = (int)sin((int)x);
    if (t>0) { y = y + 1; } // infinitely often taken
    else { a =a + 1; }
    //y = a * (int)sin((int)x);
    x = x + 1;
    //a = a + 1;
  }
  if (counter < bnd) {
    vtrace3(x,y,a);
  }
}

void mainQ(int x, int y, int a) {
  vloop(x, y, a);
}
void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}

