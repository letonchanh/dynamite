
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int a, b, x, y, z;
  a = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();

  if (z >= 4) {
    z = z + 1;
    if (x >= 0) {
      z = z + 1;
    } else {
      z = z - 1;
    }

    if (y >= 2 && y <= 5) {
      while (x >= 0) {
	a = z * z;
	b = y * z;
	x = a - b;
      }
    }
  }
  return 0;
}
