
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int x, y, z;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();

  z = 4;

  if (x <= y - 1) {
    while (x <= y - 1) {
      y = z * z;
      x = y;
      y = y + 1;
    }
  }
  return 0;
}
