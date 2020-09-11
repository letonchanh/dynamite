
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int x, y, z;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();

  if (x >= -1) {
    if (y <= -10) {
      while (x >= 0) {
	if (y <= -10) {
	  z = x * y;
	  x = x - 2 * y;
	}
      }
    }
  }
  return 0;
}
