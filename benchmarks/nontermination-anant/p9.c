
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int x, y;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();

  if (x >= 1) {
    while (x >= 0) {
      if (y >= 32) {
	if (__VERIFIER_nondet_int() > 0) {
	  x = 1;
	  y = 15;
	} else {
	  x = __VERIFIER_nondet_int();
	  y = x;
	}
      }
    }
  }
  return 0;
}
