//#define assert(b) { if (!b) __VERIFIER_error(); }
//#define f(xx,yy) (xx + 0 + 0)
#define f(xx,yy) xx

void main() {
  int x, y, tx, ty;
  int dup = 0;
  if (y < 0) {
    while( x >=0 ) {
      if(dup) {
	if ( f(tx, ty) <= f(x, y) ) __VERIFIER_error();
	if ( f(x, y)   < 0        ) __VERIFIER_error();
      }
      if(!dup && __VERIFIER_nondet_int()) { tx = x; ty = y; dup = 1; }
      x = x + y;
    }
  }
  return;
}
