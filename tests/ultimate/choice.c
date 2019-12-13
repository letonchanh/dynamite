#define f1(xx,yy) (xx)
#define f2(xx,yy) (xx + yy)
#define f3(xx,yy) (yy)
void main() {
  int x, y, tx, ty, x0, y0;
  int dup = 0;
  while (x>0 && y>0) {
    // Instrument
    if(dup) {
      if ( !(f1(tx, ty) > f1(x, y) &&  f1(tx, ty)  >= 0 )) {
        if ( !(f2(tx, ty) > f2(x, y) &&  f2(tx, ty)  >= 0 )) {
          //if ( !(f3(tx, ty) > f3(x, y) &&  f3(tx, ty)  >= 0 )) {
          __VERIFIER_error();
        }}//}
    }
    if(!dup && __VERIFIER_nondet_int()) { tx = x; ty = y; dup = 1; }
    // BODY
    x0 = x;
    y0 = y;
    if (__VERIFIER_nondet_int()) {
      x = x0-1;
      y = x0;
    } else {
      x = y0-2;
      y = x0+1;
    }
  }
  return;
}
