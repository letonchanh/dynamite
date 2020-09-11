
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int w, x, y, z;
  w = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();
  
  if (z >= 5) {
    if (y <= 2) {
      if (w <= -5) {
	while (x >= y) {
	  x = -1 * z * w;
	  z = z + 1;
	  w = w - 1;
	}
      }
    }
  }
  return 0;
}
