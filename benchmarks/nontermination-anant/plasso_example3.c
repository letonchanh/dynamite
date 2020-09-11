
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int i, j, k;
  i = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();

  if (j >= 1) {
    if (k >= 1) {
      while (i >= 0) {
	i = j * k;
	j = j + 1;
	k = k + 1;
      }
    }
  }
  return 0;
}
