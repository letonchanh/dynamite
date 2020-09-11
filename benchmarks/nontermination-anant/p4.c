
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int w, x, y, z;
  w = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();

  if (z >= 4) {
    z = z + 1;

    if (x >= 0) {
      if (w <= -5) {
	z = z + 1;
      } else {
	return 0;
    } else {
      z = z - 1;
    }

    /*
    if (__VERIFIER_nondet_int() > 0) {
      if (! (x < 0)) { return; }
      z = z - 1;
      return;
    }
    */
    while (x >= w) {
      /*
      if (__VERIFIER_nondet_int() > 0) {
	if (! (x < 0)) { return; }
	z = z - 1;
	return;
      }
      */
      /*
      if (z <= 8) {
	;
      } else {
	;
      }
      */
      x = z * z;
      w = w - 1;
    }
    /*
    if (__VERIFIER_nondet_int() > 0) {
      if (! (x < 0)) { return; }
      z = z - 1;
      return;
    }
    */
  }
  
  return 0;
}
