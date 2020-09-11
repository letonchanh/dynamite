
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int x, y, z;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();

  z = 2;
  if (x >= y) {
    x = 5;
    y = 6;

    if (z >= 0) {
      while (x <= y - 1) {
	y = z * z;
	x = y;
	y = y + 1;
      }
    }
  }
  return 0;
}
