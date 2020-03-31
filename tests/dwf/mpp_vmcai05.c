/* Example from Aaron R. Bradley, Zohar Manna, Henny B. Sipma 
   Termination of Polynomial Programs. VMCAI 2005 */

#include<stdio.h>
#include<stdlib.h>

int __VERIFIER_nondet_int() {
   return rand() % 11 - 5;
}

//extern int __VERIFIER_nondet_int(void);

void vtrace1(int x, int y, int z) {
}

void vtrace2(int x, int y, int z) {
}

void vtrace3(int x, int y, int z) {
}

void vloop(int x, int y, int z) {
    vtrace1(x, y, z);
    int bnd = 500;
    int counter = 0;

    //int tx, ty, tz;
    //int dup = 0;

    while (x >= 0) {
        if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(x, y, z);

        //if(dup) {
        //    if ( !(f1(tx, ty, tz) > f1(x, y, z) &&  f1(tx, ty, tz)  >= 0 )) {
        //    //if ( !(f2(tx, ty) > f2(x, y) &&  f2(tx, ty)  >= 0 )) {
        //    //if ( !(f3(tx, ty) > f3(x, y) &&  f3(tx, ty)  >= 0 )) {
        //        __VERIFIER_error();
        //    }//}}
        //}
        //if(!dup && __VERIFIER_nondet_int()) { 
        //    tx = x; ty = y; tz = z; dup = 1; }

        int x0 = x;
        int y0 = y;
        int z0 = z;

        if (__VERIFIER_nondet_int()) {
            x = x0 + z0;
            y = y0 + 1;
            z = z0 - 2;
        } else {
            x = x0 + y0;
            y = y0 - 2;
        }
    }

    if (counter < bnd) {
        vtrace3(x, y, z);
    }
}

void mainQ(int x, int y, int z) {
    vloop(x, y, z);

}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}

