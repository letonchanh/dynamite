#include<stdio.h>
#include<stdlib.h>

int __VERIFIER_nondet_int() {
   return rand() % 5 - 6;
}

void vtrace1(int x, int y) {
}

void vtrace2(int x, int y) {
}

void vtrace3(int x, int y) {
}

void vloop(int x, int y) {
    vtrace1(x, y);
    int bnd = 500;
    int counter = 0;

    while (x > 0 && y > 0) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(x, y);

	int x0 = x;
	int y0 = y;

	if (__VERIFIER_nondet_int() >= 0) {
	    x = x0 - 1;
	    y = x0;
	} else {
            x = y0 - 2;
            y = x0 + 1;
        }
    }

    if (counter < bnd) {
        vtrace3(x, y);
    }
}

void mainQ(int x, int y) {
    vloop(x, y);

}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

