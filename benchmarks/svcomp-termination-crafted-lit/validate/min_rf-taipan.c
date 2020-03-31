/* 
 * Terminating program which has a r.f. based on minimum
 *
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */

#define f1(x, y, z) (x)
#define f2(x, y, z) (y)
//#define f3(x, y, z) (y - z)
//#define f4(x, y, z) (x)

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x,y;
    int z;

    int tx, ty, tz;
    int dup = 0;

    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();

    while (y > 0 && x > 0) {
      if(dup) {
            if ( !(f1(tx, ty, tz) > f1(x, y, z) &&  f1(tx, ty, tz)  >= 0 )) {
            if ( !(f2(tx, ty, tz) > f2(x, y, z) &&  f2(tx, ty, tz)  >= 0 )) {
            //if ( !(f3(tx, ty, tz) > f3(x, y, z) &&  f3(tx, ty, tz)  >= 0 )) {
            //if ( !(f4(tx, ty, tz) > f3(x, y, z) &&  f4(tx, ty, tz)  >= 0 )) {
                __VERIFIER_error();
            }}//}}
      }
      if(!dup && __VERIFIER_nondet_int()) { 
            tx = x; ty = y; tz = z; dup = 1; }

      if (x>y) {
          z = y;
      } else {
          z = x;
      }
      if (__VERIFIER_nondet_int() != 0) {
          y = y+x;
          x = z-1;
          z = y+z;
      } else {
          x = y+x;
          y = z-1;
          z = x+z;
      }
    }
    return 0;
}
