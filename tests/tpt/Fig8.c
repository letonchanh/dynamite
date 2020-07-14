
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    	int x, y, z;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = __VERIFIER_nondet_int();
	while (x >= y) {
		if (z > 0) {
			z = z - 1;
			x = x + z;
		} else {
			y = y + 1;
		}
	}
	return 0;
}
