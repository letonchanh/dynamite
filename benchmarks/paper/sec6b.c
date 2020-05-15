/* 
 * Used in Section 6
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
  int x = __VERIFIER_nondet_int();

  while(x < 1000) {
    x = x + 1;
  }
  return 0;
}
