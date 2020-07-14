
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    	int x;
	x = __VERIFIER_nondet_int();
	if (x >= 0) {
		while (x*x <= 100) {
			x = 2*x + 1;
		}
	}
	return 0;
}
