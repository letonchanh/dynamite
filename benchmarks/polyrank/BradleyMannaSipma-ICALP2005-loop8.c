
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    	int y1, y2;
	y1 = __VERIFIER_nondet_int();
	y2 = __VERIFIER_nondet_int();
	if (y2 >= 1) {
		while (y2 != 1) {
			if (y1 >= 101) {
				y1 = y1 - 10;
				y2 = y2 - 1;
    			} else {
	    			y1 = y1 + 11;
			}
		}
	}
	return 0;
}
