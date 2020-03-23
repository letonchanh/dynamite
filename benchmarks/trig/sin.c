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

  while (y + a < 42) {
    int t = (int)sin((int)x);
    if (t>0) { y = y + 1; }
    else { a = a + 1; }
    //y = a * sin(x);
    x = x + 1;
  }
  return 0;
}
