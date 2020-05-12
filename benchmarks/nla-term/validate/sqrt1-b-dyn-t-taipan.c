// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/nla-digbench/sqrt1.c
/* Compute the floor of the square root of a natural number */

#define f1(aa, nn) (nn - (aa+1)*(aa+1))
#define f2(ss, nn) (nn - ss)

extern void abort(void); 
//void reach_error(){}
extern int __VERIFIER_nondet_int(void);
//extern int __VERIFIER_assert(int);
//extern void abort(void); 
//void assume_abort_if_not(int cond) { 
//  if(!cond) {abort();}
//}

void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        { __VERIFIER_error(); abort(); }
    }
    return;
}


int main() {
    int n, a, s, t;

    int ta, ts, tn;
    int dup = 0;

    n = __VERIFIER_nondet_int();
    a = 0;
    s = 1;
    t = 1;

    while ((t + 1) * (t + 1) <= 4*n) {
    // while (s <= n) {
      __VERIFIER_assert(t == 2*a + 1);
      //__VERIFIER_assert(s == (a + 1) * (a + 1));
      //__VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);
      __VERIFIER_assert(t*t + 2*t + 1 == 4*s);
        // the above 2 should be equiv to 
      //if (!(s <= n))break;

        if(dup) {
            if ( !(f2(ts, tn) > f2(s, n) &&  f2(ts, tn)  >= 0 )) {
                __VERIFIER_error();
            }
        }
        if(!dup && __VERIFIER_nondet_int()) { 
          ta = a; ts = s; tn = n; dup = 1; }

        a = a + 1;
        t = t + 2;
        s = s + t;
    }

    //__VERIFIER_assert(t == 2 * a + 1);
    //__VERIFIER_assert(s == (a + 1) * (a + 1));
    //__VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);

    return 0;
}
