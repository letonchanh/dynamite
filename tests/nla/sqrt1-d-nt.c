extern int __VERIFIER_nondet_int(void);

void main(int argc, char **argv) {
    int t = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int(); 
    int m = __VERIFIER_nondet_int();
    while (t <= n*n + 1) {
        t = t + 2*m;
        n = n + 1;
    }
}
