
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x, y, z, w;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = __VERIFIER_nondet_int();
	w = __VERIFIER_nondet_int();

	z = z + 1;
	if (x >= 0) {
		if (w >= -5) {
			z = z + 1;
		}
	} else {
		z = z - 1;
	}

	while (x >= w) {
		x = z * z;
		w = w - 1;
	}
	z = z - 1;
	return 0;
}
