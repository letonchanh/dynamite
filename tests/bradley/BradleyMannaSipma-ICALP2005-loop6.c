/*
 * Program from Fig.1 of
 * 2005ICALP - Bradley,Manna,Sipma - The Polyranking Principle
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int __VERIFIER_nondet_pos() {
	int n = __VERIFIER_nondet_int();
	if (n > 0)
		return n;
	else
		return -n + 1;
}

int main() {
    	int x, y, N;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	N = __VERIFIER_nondet_int();
	if (x + y >= 0) {
		while (x <= N) {
			if (__VERIFIER_nondet_int()) {
				x = 2*x + y;// + __VERIFIER_nondet_pos();
				y = y + 1;// + __VERIFIER_nondet_pos();
    			} else {
	    			x = x + 1;// + __VERIFIER_nondet_pos();
			}
		}
	}
	return 0;
}
