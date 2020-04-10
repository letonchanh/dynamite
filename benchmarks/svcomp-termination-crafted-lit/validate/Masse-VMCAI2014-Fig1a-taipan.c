/*
 * Program from Fig.1a of
 * 2014VMCAI - Massé - Policy Iteration-Based Conditional Termination and Ranking Functions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

// Dynamite
// #define f1(a, b) (-b)
// #define f2(a, b) (a)
// #define f3(a, b) (a + b)
// #define f4(a, b) (b)

// Automizer
// #define f1(a, b) (2*a + 1)
// #define f2(a, b) (2*b + 1)

// T2
#define f1(a, b) (2*a + b)
#define f2(a, b) (3*a)
#define f3(a, b) (3*a - 2)
#define f4(a, b) (3*a - 1)
#define f5(a, b) (-2*b)

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

extern void __VERIFIER_error(void);

int main() {
    int a, b;

	int ta, tb;
	int dup = 0;

	a = __VERIFIER_nondet_int();
	b = __VERIFIER_nondet_int();
	while (a >= 0) {
		if(dup) {
            //if ( !(f1(ta, tb) > f1(a, b) &&  f1(ta, tb)  >= 0) ) {
            //if ( !(f2(ta, tb) > f2(a, b) &&  f2(ta, tb)  >= 0) ) {
            if ( !(f3(ta, tb) > f3(a, b) &&  f3(ta, tb)  >= 0) ) {
			if ( !(f4(ta, tb) > f4(a, b) &&  f4(ta, tb)  >= 0) ) {
			//if ( !(f5(ta, tb) > f5(a, b) &&  f5(ta, tb)  >= 0) ) {
                __VERIFIER_error();
            }}//}//}//}
      	}
      	if(!dup && __VERIFIER_nondet_int()) { 
            ta = a; tb = b; dup = 1; }

		a = a + b;
		if (b >= 0) {
			b = -b - 1;
		} else {
			b = -b;
		}
	}
	return 0;
}
