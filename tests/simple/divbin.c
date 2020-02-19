#include <stdio.h>
#include <stdlib.h>
#include <math.h>

void vassume(int b){
}
void vtrace1(int A, int B, int q, int b, int r){
}
void vtrace2(int A, int B, int q, int b, int r, double l){
}
void vtrace3(int A, int B, int q, int b, int r, double l){
}

extern double log(double x);

double log2(double x) {
    return log(x) / log(2.0);
}

int mainQ(int A, int B){
    vassume(A > 0 && B > 0);
 
    int q = 0;
    int r = A;
    int b = B;
    double l;

    while(1){
	    if (!(r>=b)) break;
	    b=2*b;
    }

    vtrace1(A, B, q, b, r);
    while(1){
	    //assert(A == q*b + r && r >= 0);
	    l = log2(b/B);
        vtrace2(A, B, q, b, r, l);
	    if (!(b!=B)) break;

        q = 2*q;
        b = b/2;
        if (r >= b) {
            q = q + 1;
            r = r - b;
        }
    }
    l = log2(b/B);
    vtrace3(A, B, q, b, r, l);
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

