/* extended Euclid's algorithm */

#include<stdio.h>
#include <stdlib.h>

void vtrace1(int x, int y, int a, int b, int p, int q, int r, int s) {
}

void vtrace2(int x, int y, int a, int b, int p, int q, int r, int s) {
}

void vtrace3(int x, int y, int a, int b, int p, int q, int r, int s) {
}

void vloop(int x, int y, int a, int b, int p, int q, int r, int s) {
    vtrace1(x, y, a, b, p, q, r, s);
    int bnd = 500;
    int counter = 0;

    while (1 == p * s - r * q) {
        //__VERIFIER_assert(1 == p * s - r * q);
        //__VERIFIER_assert(a == y * r + x * p);
        //__VERIFIER_assert(b == x * q + y * s);
        
	if (counter >= bnd)
            break;
        else
            counter++;

        vtrace1(x, y, a, b, p, q, r, s);

        if (a > b) {
            a = a - b;
            p = p - q;
            r = r - s;
        } else {
            b = b - a;
            q = q - p;
            s = s - r;
        }
    }
    if (counter < bnd) {
        vtrace1(x, y, a, b, p, q, r, s);
    }
}

void mainQ(int x, int y) {
    int a, b, p, q, r, s;
    //__VERIFIER_assume(x >= 1);
    //__VERIFIER_assume(y >= 1);

    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;

    vloop(x,y,a,b,p,q,r,s)
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
