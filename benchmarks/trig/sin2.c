#include <math.h>
#include <stdio.h>

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
  int x, y, a;

  while (y < 42) {
    int t = a * (int)sin((int)x);
    if (t <= a) { y = y + 1; }
    x = x + 1;
    a = a + 1;
  }
  return 0;
}

