/* 
Geometric Series
computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
*/
extern int __VERIFIER_nondet_int(void);

int main() {
    int z, k;
    int x, y, c;
    z = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();

    x = 1;
    y = 1;
    c = 1;

    while (1) {
        // __VERIFIER_assert(1 + x*z - x - z*y == 0);

        if (!(1 + x*z - x - z*y == 0))
            break;

        c = c + 1;
        x = x * z + 1;
        y = y * z;
    }
    // __VERIFIER_assert(1 + x*z - x - z*y == 0);
    return 0;
}
