/* extended Euclid's algorithm */

//WIP: nested loops

#include<stdio.h>
#include <stdlib.h>

void vtrace1(int x, int y, int a, int b, int p, int q, int r, int s, int c, int k) {
}

void vtrace2(int x, int y, int a, int b, int p, int q, int r, int s, int c, int k) {
}

void vtrace3(int x, int y, int a, int b, int p, int q, int r, int s, int c, int k) {
}

void vloop(int x, int y, int a, int b, int p, int q, int r, int s, int c, int k) {
    vtrace1(x,y,a,b,p,q,r,s,c,k);
    int bnd = 500;
    int counter = 0;

    while (b != 0) {
        if (counter >= bnd)
            break;
        else
            counter++;

        vtrace2(x,y,a,b,p,q,r,s,c,k);

        c = a;
        k = 0;

        while (c>=b) {
            //__VERIFIER_assert(a == k * b + c);
            //__VERIFIER_assert(a == y*r + x*p);
            //__VERIFIER_assert(b == x * q + y * s);
            //__VERIFIER_assert(q*x*y + s*y*y - q*x - b*y - s*y + b == 0);
            c = c - b;
            k = k + 1;
        }

        a = b;
        b = c;

        int temp;
        temp = p;
        p = q;
        q = temp - q * k;
        temp = r;
        r = s;
        s = temp - s * k;
    }
    if (counter < bnd) {
        vtrace3(x,y,a,b,p,q,r,s,c,k);
    }

}

void mainQ(int x, int y) {
    int a, b, p, q, r, s, c, k;
    //__VERIFIER_assume(x >= 1);
    //__VERIFIER_assume(y >= 1);

    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;
    c = 0;
    k = 0;

    vloop(x,y,a,b,p,q,r,s,c,k)
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}

