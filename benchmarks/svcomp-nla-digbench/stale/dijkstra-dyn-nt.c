/* Compute the floor of the square root, by Dijkstra */

//WIP: sequential loops

#include<stdio.h>
#include <stdlib.h>

void vtrace1(int n, int p, int q, int r, int h) {
}

void vtrace2(int n, int p, int q, int r, int h) {
}

void vtrace3(int n, int p, int q, int r, int h) {
}

void vloop(int n, int p, int q, int r, int h) {
    vtrace1(n,p,q,r,h);
    int bnd = 500;
    int counter = 0;

    while (p * p - n * q + q * r == 0) {
	if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(n,p,q,r,h);
        q = q / 4;
        h = p + q;
        p = p / 2;
        if (r >= h) {
            p = p + q;
            r = r - h;
        }
    }
    if (counter < bnd) {
        vtrace3(n,p,q,r,h);
    }
}

void mainQ(int n) {
    int p, q, r, h;

    p = 0;
    q = 1;
    r = n;
    h = 0;
    while (q<=n) {

        q = 4 * q;
    }
    //q == 4^n

    vloop(n,p,q,r,h)
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]));
}
