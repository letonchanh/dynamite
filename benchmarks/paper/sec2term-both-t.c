/* 
 * Used in the overview
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
  int s = 1, t = 1, c = 1;
  int k = __VERIFIER_nondet_int();

  while(t*t - 4*s + 2*t + 1 + c <= k) {
    t = t + 2;
    s = s + t;
    c = c + t;
  }
  return 0;
}
