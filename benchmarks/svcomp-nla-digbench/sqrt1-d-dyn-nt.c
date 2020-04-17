// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/nla-digbench/sqrt1.c
/* Compute the floor of the square root of a natural number */
#include<stdio.h>
#include <stdlib.h>

void vtrace1(int t, int n, int m) {
}

void vtrace2(int t, int n, int m) {
}

void vtrace3(int t, int n, int m) {
}

void vloop(int t, int n, int m) {
    vtrace1(t, n, m);
    int bnd = 500;
    int counter = 0;

    while (t <= n*n + 1) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(t, n, m);

        t = t + 2*m;
        n = n + 1;
    }

    if (counter < bnd) {
        vtrace3(t, n, m);
    }
}

void mainQ(int qt, int qn, int qm) {
    vloop(qt, qn, qm);
}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
