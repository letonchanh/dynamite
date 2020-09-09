
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    	int x, y, z;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = __VERIFIER_nondet_int();
	while (x >= y) {
		if (__VERIFIER_nondet_int()) {
			y = y + x;
			x = x + 1;
    		} else {
	    		x = x - z;
			y = y + z*z;
			z = z - 1;
		}
	}
	return 0;
}
