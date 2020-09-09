
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i, j, k, an, bn, tk;
	i = __VERIFIER_nondet_int();
	j = __VERIFIER_nondet_int();
	k = __VERIFIER_nondet_int();
	an = __VERIFIER_nondet_int();
	bn = __VERIFIER_nondet_int();
	while (((an >= i && bn >= j) || (an >= i && bn <= j) || (an <= i && bn >= j))) {
		if (an >= i && bn >= j) {
			if (__VERIFIER_nondet_int()) {
				j = j + k;
				k = k + 1;
			} else {
				i = i + 1;
			}
		} else {if (an >= i && bn <= j) {
			i = i + 1;
		} else {if (an <= i && bn >= j) {
			j = j + k;
			k = k + 1;
		}}}
	}
	return 0;
}
