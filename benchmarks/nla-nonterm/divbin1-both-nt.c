/*
  A division algorithm, by Kaldewaij
  returns A//B
*/

#include <limits.h>
/*
extern void __VERIFIER_error() __attribute__((__noreturn__));
extern unsigned __VERIFIER_nondet_unsigned_int(void);
extern void __VERIFIER_assume(int expression);
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        __VERIFIER_error();
    }
    return;
    }*/

extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_unsigned_int(void);
int main() {
  unsigned A, B;
  unsigned q, r, b;
  A = __VERIFIER_nondet_unsigned_int();
  B = __VERIFIER_nondet_unsigned_int();
  //__VERIFIER_assume(B < UINT_MAX/2);
  if (B >= UINT_MAX/2) return 0;
  //__VERIFIER_assume(B >= 1);
  if ( B < 1 ) return 0;

  if (A >= UINT_MAX/2) return 0;

    q = 0;
    r = A;
    b = B;

    while (r >= b) {
      //if (!(r >= b)) break;
      b = 2 * b;
    }

    while (A == q * b + r) {
      // __VERIFIER_assert(A == q * b + r);
        //if (!(b != B)) break;

        if (2 * (b / 2) == b) {
            q = 2 * q;
            b = b / 2;
            if (r >= b) {
                q = q + 1;
                r = r - b;
            }
        }
    }
    //__VERIFIER_assert(A == q * b + r);
    return 0;
}
