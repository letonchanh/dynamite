/*
 * Program from Fig.1a of
 * 2014VMCAI - Massé - Policy Iteration-Based Conditional Termination and Ranking Functions
 *
 * Date: 2014
 * Author: Caterina Urban
 */
#include<stdio.h>
#include<stdlib.h>

int __VERIFIER_nondet_int() {
   return rand() % 11 - 5;
}

void vtrace1(int a, int b) {
}

void vtrace2(int a, int b) {
}

void vtrace3(int a, int b) {
}

void vloop(int a, int b) {
	vtrace1(a, b);
    int bnd = 500;
    int counter = 0;

	while (a >= 0) {
		if (counter >= bnd)
            break;
        else
            counter++;
      	vtrace2(a, b);

		a = a + b;
		if (b >= 0) {
			b = -b - 1;
		} else {
			b = -b;
		}
	}
	if (counter < bnd) {
        vtrace3(a, b);
    }
}

void mainQ(int a, int b) {
    vloop(a, b);
}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

