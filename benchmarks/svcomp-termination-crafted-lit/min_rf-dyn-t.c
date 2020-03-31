/* 
 * Terminating program which has a r.f. based on minimum
 *
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */

#include<stdio.h>
#include<stdlib.h>

int __VERIFIER_nondet_int() {
   return rand() % 11 - 5;
}

void vtrace1(int x, int y, int z) {
}

void vtrace2(int x, int y, int z) {
}

void vtrace3(int x, int y, int z) {
}

void vloop(int x, int y, int z) {
    vtrace1(x, y, z);
    int bnd = 500;
    int counter = 0;

    while (y > 0 && x > 0) {
      if (counter >= bnd)
            break;
        else
            counter++;
      vtrace2(x, y, z);

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
    if (counter < bnd) {
        vtrace3(x, y, z);
    }
}

void mainQ(int x, int y) {
    int z = __VERIFIER_nondet_int();
    vloop(x, y, z);
}

void main(int argc, char **argv)
{
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
