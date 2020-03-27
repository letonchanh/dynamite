/* 
Geometric Series
computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
*/

#include<stdio.h>
#include <stdlib.h>

void vtrace1(int z, int a, int k, int x int y, int c) {
}

void vtrace2(int z, int a, int k, int x int y, int c) {
}

void vtrace3(int z, int a, int k, int x int y, int c) {
}

void vloop(int z, int a, int k, int x int y, int c) {
    vtrace1(z,a,k,x,y,c);
    int bnd = 500;
    int counter = 0;

    while (c<k) {
        //__VERIFIER_assert(z*x - x + a - a*z*y == 0);
         if (counter >= bnd)
            break;
        else
            counter++;

        vtrace2(z,a,k,x,y,c);
        c = c + 1;
        x = x * z + a;
        y = y * z;
    }
    if (counter < bnd) {
        vtrace3(z,a,k,x,y,c);
    }
    //__VERIFIER_assert(z*x - x + a - a*z*y == 0);
}

void mainQ(int z, int a, int k) {
    int x, y, c;

    x = a;
    y = 1;
    c = 1;


    vloop(z,a,k,x,y,c);
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2], atoi(argv[3])));
}
~
