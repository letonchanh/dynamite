
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x, y, z;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = __VERIFIER_nondet_int();

	if (z >= 4) {
		z = z + 1;

		if (x >= 0) {
			z = z + 1;
		} else {
			z = z - 1;
		}

		if (y >= 2) {
			while (x >= 0) {
				x = z * z - y * z;
			}
		}
	}
	return 0;
}
