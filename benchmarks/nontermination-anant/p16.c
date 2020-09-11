
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int x, y, z;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();

  if (x >= -1) {
    if (y >= -10) {
      while (x >= 1 && y >= -10) {
	z = x * y;
	x = y;
	x = y + 1;
      }
    }
  }
  return 0;
}
