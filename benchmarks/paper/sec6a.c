/* 
 * Used in Section 6
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();

  while(x >= 0) {
    x = x + y;
  }
  return 0;
}
