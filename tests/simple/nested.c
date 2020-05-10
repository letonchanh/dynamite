extern int __VERIFIER_nondet_int(void);

void main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int(); 

  while (x >= 0) {
    while (y <= 0) {
      y = y + 1;
    }
    x = x - y;
  }
  if (y > 0) {
    while (z <= 0) {
      z = z + y;
    }
  }
  /*
  while (y < 0) {
    y = y + 1;
    while (x > 10) {
      x = x + 1;
    }
    while (x < 20) {
      x = x + 1;
    }
  }

  while (x >= 0) {
    while (y >= 0) {
      y = y - 1;
    }
    x = x + y;
  }
  */
}
