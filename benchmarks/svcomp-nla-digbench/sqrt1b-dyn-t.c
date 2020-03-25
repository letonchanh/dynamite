// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/nla-digbench/sqrt1.c
/* Compute the floor of the square root of a natural number */
#include<stdio.h>
#include <stdlib.h>

void vtrace1(int a, int t, int s, int n) {
}

void vtrace2(int a, int t, int s, int n) {
}

void vtrace3(int a, int t, int s, int n) {
}

void vloop(int a, int t, int s, int n) {
    vtrace1(a, t, s, n);
    int bnd = 500;
    int counter = 0;

    while (t*t + 2*t + 1 <= 4*n) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(a, t, s, n);

        a = a + 1;
        t = t + 2;
        s = s + t;
    }

    if (counter < bnd) {
        vtrace3(a, t, s, n);
    }
}

void mainQ(int n) {
    int a, s, t;

    a = 0;
    s = 1;
    t = 1;

    vloop(a, t, s, n);

}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]));
}
