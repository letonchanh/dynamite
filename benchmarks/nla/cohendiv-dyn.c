/*
  Cohen's integer division
  returns x % y
  http://www.cs.upc.edu/~erodri/webpage/polynomial_invariants/cohendiv.htm
*/
#include<stdio.h>
#include <stdlib.h>

//WIP: nested loops

void vtrace1(int x, int y, int q, int r, int a, int b) {
}

void vtrace2(int x, int y, int q, int r, int a, int b) {
}

void vtrace3(int x, int y, int q, int r, int a, int b) {
}

void vloop1(int x, int y, int q, int r, int a, int b) {
    vtrace1(a,y,q,r,a,b);
    int bnd = 500;
    int counter = 0;

    while (r>=y) {
	if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(a,y,q,r,a,b);
	a = 1;
	b = y;

	while (r >= 2*b) {            

	    a = 2 * a;
	    b = 2 * b;
	}
	r = r - b;
	q = q + a;
    }
    if (counter < bnd) {
        vtrace3(a,y,q,r,a,b);
    }
}

void main(int x, int y) {
    int q, r, a, b;

    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();

    __VERIFIER_assume(y >= 1);

    if (y >= 1){
        q = 0;
        r = x;
        a = 0;
        b = 0;
        
	vloop1(x,y,q,r,a,b);
    }
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
