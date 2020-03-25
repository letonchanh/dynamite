// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/nla-digbench/sqrt1.c
/* Compute the floor of the square root of a natural number */

#define f1(aa, nn) (nn - (aa+1)*(aa+1))

extern void abort(void); 
void reach_error(){}
extern int __VERIFIER_nondet_int(void);
extern void abort(void); 
void assume_abort_if_not(int cond) { 
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        {reach_error();abort();}
    }
    return;
}


int main() {
    int n, a, s, t;

    int ta, tn;
    int dup = 0;

    n = __VERIFIER_nondet_int();
    a = 0;
    s = 1;
    t = 1;

    while ((a + 1) * (a + 1) <= n) {
    // while (s <= n) {
      //__VERIFIER_assert(t == 2*a + 1);
      //__VERIFIER_assert(s == (a + 1) * (a + 1));
      //__VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);
        // the above 2 should be equiv to 
      //if (!(s <= n))break;

        if(dup) {
            if ( !(f1(ta, tn) > f1(a, n) &&  f1(ta, tn)  >= 0 )) {
                __VERIFIER_error();
            }
        }
        if(!dup && __VERIFIER_nondet_int()) { 
          ta = a; tn = n; dup = 1; }

        a = a + 1;
        t = t + 2;
        s = s + t;
    }

    //__VERIFIER_assert(t == 2 * a + 1);
    //__VERIFIER_assert(s == (a + 1) * (a + 1));
    //__VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);

    return 0;
}