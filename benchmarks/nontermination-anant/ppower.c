
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int n, i, exp;
  n = __VERIFIER_nondet_int();
  i = __VERIFIER_nondet_int();
  exp = __VERIFIER_nondet_int();

  if (n >= 2) {
    i = 1;
    exp = 1;
    while (i <= exp) {
      exp = exp * n;
      i = i + 1;
    }
  }
  return 0;
}
