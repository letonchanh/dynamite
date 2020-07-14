
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    	int i, j, M, N;
	i = __VERIFIER_nondet_int();
	j = __VERIFIER_nondet_int();
	M = __VERIFIER_nondet_int();
	N = __VERIFIER_nondet_int();
	while (i < M || j < N) {
		i = i + 1;
		j = j + 1;
	}
	return 0;
}
