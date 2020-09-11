
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int x, y, z;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();

  if (z >= 2) {
    if (y >= 3) {
      while (z >= -5) {
	while (x >= 0) {
	  x = z / y;
	  y = y + 1;
	  z = z + 1;
	}
      }
    }
  }
  return 0;
}
