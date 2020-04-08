// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/nla-digbench/sqrt1.c
/* Compute the floor of the square root of a natural number */
#include<stdio.h>
#include <stdlib.h>

void vtrace1(int t, int n) {
}

void vtrace2(int t, int n, int tmp) {
}

void vtrace3(int t, int n, int tmp) {
}

void vloop(int t, int n) {
    vtrace1(t, n);
    int bnd = 500;
    int counter = 0;

    int tmp = n*n;
    while (t <= tmp) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(t, n, tmp);

        t = t + 2;
        n = n + 1;
        tmp = n*n;
    }

    if (counter < bnd) {
        vtrace3(t, n, tmp);
    }
}

void mainQ(int t, int n) {
    vloop(t, n);

}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
