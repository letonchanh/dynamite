
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

void f(int x, int y, int z) {
  if (! (z >= 4)) { return; }
  z = z + 1;

  if (x >= 0) {
    z = z + 1;
  } else {
    z = z - 1;
  }

  if (! (y >= 1)) { return; }
  if (! (y <= 5)) { return; }

  while (x >= 0) {
    x = z*z - y*z;
    z = z + 1;
  }
        z = z - 1;
}

int main() {
  int x, y, z;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();
  f(x, y, z);
  return 0;
}
