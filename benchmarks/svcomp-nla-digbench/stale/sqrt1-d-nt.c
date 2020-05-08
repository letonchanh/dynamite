// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/nla-digbench/sqrt1.c
/* Compute the floor of the square root of a natural number */
void main(int argc, char **argv) {
    int t, n, m;
    while (t <= n*n + 1) {
        t = t + 2*m;
        n = n + 1;
    }
}
