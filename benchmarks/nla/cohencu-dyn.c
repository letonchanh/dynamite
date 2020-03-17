/*
Printing consecutive cubes, by Cohen
http://www.cs.upc.edu/~erodri/webpage/polynomial_invariants/cohencu.htm
*/
#include<stdio.h>
#include <stdlib.h>

void vtrace1(int x, int y, int z, int k, int c) {
}

void vtrace2(int x, int y, int z, int k, int c) {
}

void vtrace3(int x, int y, int z, int k, int c) {
}

void vloop(int a, int n, int x, int y, int z) {
    vtrace1(a, n, x, y, z);
    int bnd = 500;
    int counter = 0;

    while (n<=a) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(a, n, x, y, z);
        n = n + 1;
        x = x + y;
        y = y + z;
        z = z + 6;
    }
    if (counter < bnd) {
        vtrace3(a, n, x, y, z);
    }
}

void mainQ(int a) {
    int n, x, y, z;
    n = 0;
    x = 0;
    y = 1;
    z = 6;

    vloop(a, n, x, y, z);

}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
