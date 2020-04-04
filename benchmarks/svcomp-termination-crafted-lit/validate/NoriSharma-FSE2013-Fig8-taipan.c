/*
 * Program from Fig.8 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

 /* [-b, b, a, a + b] */

#define f1(x, y, z) (x - y)
#define f2(x, y, z) (z)

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int c, u, v, w, x, y, z;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = __VERIFIER_nondet_int();
    u = x;
    v = y;
    w = z;
    c = 0;

    int tx, ty, tz;
    int dup = 0;

    while (x >= y) {
      if(dup) {
            if ( !(f1(tx, ty, tz) > f1(x, y, z) &&  f1(tx, ty, tz)  >= 0 )) {
            if ( !(f2(tx, ty, tz) > f2(x, y, z) &&  f2(tx, ty, tz)  >= 0 )) {
            //if ( !(f3(tx, ty, tz) > f3(x, y, z) &&  f3(tx, ty, tz)  >= 0 )) {
                __VERIFIER_error();
            }}//}
      }
      if(!dup && __VERIFIER_nondet_int()) { 
            tx = x; ty = y; tz = z; dup = 1; }
    	
        c = c + 1;
    	if (z > 1) {
    		z = z - 1;
    		x = x + z;
    	} else {
    		y = y + 1;
    	}
    }
    return 0;
}
