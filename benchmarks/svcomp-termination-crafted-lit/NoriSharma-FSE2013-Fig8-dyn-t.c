/*
 * Program from Fig.8 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

#include<stdio.h>
#include<stdlib.h>

int __VERIFIER_nondet_int() {
   return rand() % 11 - 5;
}

void vtrace1(int c, int x, int y, int z) {
}

void vtrace2(int c, int x, int y, int z) {
}

void vtrace3(int c, int x, int y, int z) {
}

void vloop(int c, int x, int y, int z) {
    vtrace1(c, x, y, z);
    int bnd = 500;
    int counter = 0;

    while (x >= y) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(c, x, y, z);

        c = c + 1;
        if (z > 1) {
                z = z - 1;
                x = x + z;
        } else {
                y = y + 1;
        }
    }

    if (counter < bnd) {
        vtrace3(c, x, y, z);
    }
}


void mainQ(int x, int y, int z) {
    int c, u, v, w;
    u = x;
    v = y;
    w = z;
    c = 0;
    vloop(c, x, y, z);
}

void main(int argc, char **argv)
{
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
