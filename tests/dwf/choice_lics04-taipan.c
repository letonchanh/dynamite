#include<stdio.h>
#include<stdlib.h>

#define f1(xx, yy) (xx + yy)
//#define f2(xx, yy) (xx)
//#define f3(xx, yy) (yy)

//int __VERIFIER_nondet_int() {
//   return rand() % 5 - 6;
//}

extern int __VERIFIER_nondet_int(void);

//void vtrace1(int x, int y) {
//}

//void vtrace2(int x, int y) {
//}

//void vtrace3(int x, int y) {
//}

void vloop(int x, int y) {
    //vtrace1(x, y);
    //int bnd = 500;
    //int counter = 0;

    int tx, ty;
    int dup = 0;

    while (x > 0 && y > 0) {
        //if (counter >= bnd)
        //    break;
        //else
        //    counter++;
        //vtrace2(x, y);

        if(dup) {
            if ( !(f1(tx, ty) > f1(x, y) &&  f1(tx, ty)  >= 0 )) {
            //if ( !(f2(tx, ty) > f2(x, y) &&  f2(tx, ty)  >= 0 )) {
            //if ( !(f3(tx, ty) > f3(x, y) &&  f3(tx, ty)  >= 0 )) {
                __VERIFIER_error();
            }//}}
        }
        if(!dup && __VERIFIER_nondet_int()) { 
            tx = x; ty = y; dup = 1; }

        int x0 = x;
        int y0 = y;

        if (__VERIFIER_nondet_int()) {
            x = x0 - 1;
            y = x0;
        } else {
            x = y0 - 2;
            y = x0 + 1;
        }
    }

    //if (counter < bnd) {
    //    vtrace3(x, y);
    //}
}

void mainQ(int x, int y) {
    vloop(x, y);

}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

