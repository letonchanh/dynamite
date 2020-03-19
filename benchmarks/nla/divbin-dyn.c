/*
  A division algorithm, by Kaldewaij
  returns A//B
*/

//WIP: sequential loops

#include <limits.h>
#include<stdio.h>
#include <stdlib.h>

void vtrace1(int A, int B, int q, int r, int b) {
}

void vtrace2(int A, int B, int q, int r, int b) {
}

void vtrace3(int A, int B, int q, int r, int b) {
}


void vloop(int A, int B, int q, int r, int b) {
    vtrace1(A,B,q,r,b);
    int bnd = 500;
    int counter = 0;

    while (b != B) {
        //__VERIFIER_assert(A == q * b + r);
	if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(A,B,q,r,b);

        q = 2 * q;
        b = b / 2;
        if (r >= b) {
            q = q + 1;
            r = r - b;
        }
    }
    if (counter < bnd) {
        vtrace3(A,B,q,r,b);
    }
}

void mainQ(int A, int B) {
    unsigned q, r, b;
    //__VERIFIER_assume(B < UINT_MAX/2);
    //__VERIFIER_assume(B >= 1);

    q = 0;
    r = A;
    b = B;

    while (1) {
        if (!(r >= b)) break;
        b = 2 * b;
    }

    vloop(A,B,q,r,b)
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
