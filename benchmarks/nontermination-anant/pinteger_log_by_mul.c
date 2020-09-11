
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int n, d, log, firstMultiply;
  n = __VERIFIER_nondet_int();
  d = __VERIFIER_nondet_int();
  log = __VERIFIER_nondet_int();
  firstMultiply = __VERIFIER_nondet_int();

  if (n >= 1) {
    if (d >= 0) {
      if (d < 2) {
	log = 0;
	firstMultiply = d;
	while (d <= n) {
	  log = log + 1;
	  d = d * firstMultiply;
	}
      }
    }
  }
  return 0;
}
