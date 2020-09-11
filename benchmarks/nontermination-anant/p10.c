
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int a, b, x, y, z;
  a = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();
  
  if (x >= 1) {
    if (b < 0) {
      if (a >= 0) {
	while (x >= y && z < 42) {
	  if (__VERIFIER_nondet_int() > 0) {
	    x = 1;
	    y = 15;
	  } else {
	    x = __VERIFIER_nondet_int();
	    z = a * b;
	    a = a + 1;
	  }
	}
      }
    }
  }
  return 0;
}
