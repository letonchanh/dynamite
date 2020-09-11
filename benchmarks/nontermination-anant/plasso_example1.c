
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int i, j, k;
  i = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();

  if (j >= 2) {
    if (k >= 3) {
      while (i >= 0) {
	i = j * k;
      }
    }
  }
  return 0;
}
