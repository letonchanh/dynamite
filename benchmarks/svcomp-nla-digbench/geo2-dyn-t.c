/* 
Geometric Series
computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
*/

#include<stdio.h>
#include <stdlib.h>

void vtrace1(int z, int k, int x, int y, int c) {
}

void vtrace2(int z, int k, int x, int y, int c) {
}

void vtrace3(int z, int k, int x, int y, int c) {
}

void vloop(int z, int k, int x, int y, int c) {
    vtrace2(z,k,x,y,c);
    int bnd = 500;
    int counter = 0;

    while (c<k) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(z,k,x,y,c);

        //__VERIFIER_assert(1 + x*z - x - z*y == 0);


        c = c + 1;
        x = x * z + 1;
        y = y * z;
    }
    if (counter < bnd) {
        vtrace3(z,k,x,y,c);
    }
    //__VERIFIER_assert(1 + x*z - x - z*y == 0);
}

void mainQ(int z, int k) {
    int x, y, c;

    x = 1;
    y = 1;
    c = 1;

    vloop(z,k,x,y,c)

    while (1) {
        __VERIFIER_assert(1 + x*z - x - z*y == 0);

        if (!(c < k))
            break;

        c = c + 1;
        x = x * z + 1;
        y = y * z;
    }
    __VERIFIER_assert(1 + x*z - x - z*y == 0);
    return 0;
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
