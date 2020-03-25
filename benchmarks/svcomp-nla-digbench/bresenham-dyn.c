/*
  Bresenham's line drawing algorithm 
  from Srivastava et al.'s paper From Program Verification to Program Synthesis in POPL '10 
*/

#include<stdio.h>
#include <stdlib.h>

void vtrace1(int X, int Y, int v, int x, int y) {
}

void vtrace2(int X, int Y, int v, int x, int y) {
}

void vtrace3(int X, int Y, int v, int x, int y) {
}

void vloop(int X, int Y, int v, int x, int y) {
    vtrace1(X, Y, v, x, y);
    int bnd = 500;
    int counter = 0;

    while (x<= X) {
	if (counter >= bnd)
            break;
        else
            counter++;

        vtrace2(X, Y, v, x, y);

        if (v < 0) {
            v = v + 2 * Y;
        } else {
            v = v + 2 * (Y - X);
            y++;
        }
        x++;
    }
    if (counter < bnd) {
        vtrace3(X, Y, v, x, y);
    }
}

void mainQ(int X, int Y) {
    int v, x, y;
    
    v = 2 * Y - X;
    y = 0;
    x = 0;

    vloop(X, Y, v, x, y);
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
