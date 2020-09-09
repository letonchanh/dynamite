

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
    	int x, y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x >= y) {
		if (__VERIFIER_nondet_int()) {
			x = x - 1 - __VERIFIER_nondet_pos();
    		} else {
	    		y = y + 1 + __VERIFIER_nondet_pos();
		}
	}
	return 0;
}
