
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int n, d, log;
  n = __VERIFIER_nondet_int();
  d = __VERIFIER_nondet_int();
  log = __VERIFIER_nondet_int();

  if (n >= 1) {
    if (d >= 2) {
      log = 0;
      while (n >= 0) {
	n = n / d;
	log = log + 1;
      }
    }
  }
  return 0;
}
