
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int z;
  z = __VERIFIER_nondet_int();

  if (z >= 3) {
    while (z >= 3) {
      z = __VERIFIER_nondet_int();
    }
  }
  return 0;
}
