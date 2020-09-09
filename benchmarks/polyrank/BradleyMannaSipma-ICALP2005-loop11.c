
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int __VERIFIER_nondet_pos() {
    int n = __VERIFIER_nondet_int();
    if (n > 0)
        return n;
    else
        return -n + 1;
}

int main() {
    int p, q, x, y, n, N, e, __cil_tmp_p, __cil_tmp_q, __cil_tmp_x, __cil_tmp_y, __cil_tmp_n, __cil_tmp_N, __cil_tmp_e;
    p = __VERIFIER_nondet_int();
    q = __VERIFIER_nondet_int();
    x = 0;
    y = 0;
    n = __VERIFIER_nondet_int();
    N = __VERIFIER_nondet_int();
    e = __VERIFIER_nondet_int();
    //__cil_tmp_p = __VERIFIER_nondet_int();
    //__cil_tmp_q = __VERIFIER_nondet_int();
    //__cil_tmp_x = __VERIFIER_nondet_int();
    //__cil_tmp_y = __VERIFIER_nondet_int();
    //__cil_tmp_n = __VERIFIER_nondet_int();
    //__cil_tmp_N = __VERIFIER_nondet_int();
    //__cil_tmp_e = __VERIFIER_nondet_int();
    if (p >= 0 && q >= 1 && N >= 0) {
        while (x + y <= N || (x + y <= N && n + e >= 2 * q + 1) || p >= 0) {
            __cil_tmp_p = p;
            __cil_tmp_q = q;
            __cil_tmp_x = x;
            __cil_tmp_y = y;
            __cil_tmp_n = n;
            __cil_tmp_N = N;
            __cil_tmp_e = e;
            if (x + y <= N && !(n + e >= 2 * q + 1)) {
                x = __VERIFIER_nondet_int();
                            y = __VERIFIER_nondet_int();
                n = __VERIFIER_nondet_int();
                                e = __VERIFIER_nondet_int();
                if (!(__cil_tmp_x + __cil_tmp_e - __cil_tmp_q <= x &&
                      x <= __cil_tmp_x + __cil_tmp_e + __cil_tmp_q &&
                      __cil_tmp_y + __cil_tmp_n - __cil_tmp_q <= y &&
                      y <= __cil_tmp_y + __cil_tmp_n + __cil_tmp_q &&
                      __cil_tmp_n + __cil_tmp_e + 1 <= n + e &&
                      n + e <= __cil_tmp_n + __cil_tmp_e + __cil_tmp_p))
                    break;
            } else if (x + y <= N && n + e >= 2 * q + 1) {
                if (__VERIFIER_nondet_int()) {
                    x = __VERIFIER_nondet_int();
                    y = __VERIFIER_nondet_int();
                    n = __VERIFIER_nondet_int();
                    e = __VERIFIER_nondet_int();
                    if (!(__cil_tmp_x + __cil_tmp_e - __cil_tmp_q <= x &&
                          x <= __cil_tmp_x + __cil_tmp_e + __cil_tmp_q &&
                          __cil_tmp_y + __cil_tmp_n - __cil_tmp_q <= y &&
                          y <= __cil_tmp_y + __cil_tmp_n + __cil_tmp_q &&
                          __cil_tmp_n + __cil_tmp_e + 1 <= n + e &&
                          n + e <= __cil_tmp_n + __cil_tmp_e + __cil_tmp_p))
                        break;
                } else {
                    x = __VERIFIER_nondet_int();
                    y = __VERIFIER_nondet_int();
                    if (!(__cil_tmp_x + __cil_tmp_e - __cil_tmp_q <= x &&
                          x <= __cil_tmp_x + __cil_tmp_e + __cil_tmp_q &&
                          __cil_tmp_y + __cil_tmp_n - __cil_tmp_q <= y &&
                          y <= __cil_tmp_y + __cil_tmp_n + __cil_tmp_q))
                        break;
                }
                } else {
                    n = __VERIFIER_nondet_int();
                    e = __VERIFIER_nondet_int();
                    p = p - 1;
                    q = q / 2;
                if (!(n + e <= -(__cil_tmp_n + __cil_tmp_e)))
                    break;
            }
        }
    }
    return 0;
}
