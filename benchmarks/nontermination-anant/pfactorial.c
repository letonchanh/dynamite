
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int n, i, fact;
  n = __VERIFIER_nondet_int();
  i = __VERIFIER_nondet_int();
  fact = __VERIFIER_nondet_int();

  if (n >= 1) {
    fact = 2;
    i = 1;
    while (i <= fact) {
      fact = fact * i;
      i = i + 1;
    }
  }
  return 0;
}
