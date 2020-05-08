#include <stdlib.h>

int main() {
    int n, a, s, t, k, c;
    a = 0;
    s = 1;
    t = 1;
    c = 0;
   while (t*t - 4*s + 2*t + 1 +c <= k) {
   // while(a < n) { // works
        a = a + 1;
        t = t + 2;
        s = s + t;
	c = c + 1;
    }
    return 0;
}
