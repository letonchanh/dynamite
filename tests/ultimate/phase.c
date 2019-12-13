// Enter Code here ...
#define f1(xx,yy) (xx)
#define f2(xx,yy) (yy)
void main() {
  int x, y, tx, ty, x0, y0;
  int dup = 0;
  while (x>=0) {
    // Instrument
    if(dup) {
      if ( !(f1(tx, ty) > f1(x, y) &&  f1(tx, ty)  >= 0 )) {
        if ( !(f2(tx, ty) > f2(x, y) &&  f2(tx, ty)  >= 0 )) {
          __VERIFIER_error();
        }}
    }
    if(!dup && __VERIFIER_nondet_int()) { tx = x; ty = y; dup = 1; }
    // BODY
    x = x + y;
    y = y - 1;
  }
  return;
}
