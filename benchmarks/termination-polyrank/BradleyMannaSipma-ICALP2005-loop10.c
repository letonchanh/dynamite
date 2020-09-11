
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
    int x, y, z, w, __cil_tmp_x, __cil_tmp_y, __cil_tmp_z, __cil_tmp_w;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    z = __VERIFIER_nondet_int();
    w = __VERIFIER_nondet_int();
    //__cil_tmp_x = __VERIFIER_nondet_int();
    //__cil_tmp_y = __VERIFIER_nondet_int();
    //__cil_tmp_z = __VERIFIER_nondet_int();
    //__cil_tmp_w = __VERIFIER_nondet_int();
    if (x >= 0 && y >= 0 && z >= 0 && x >= y) {
        while (y >= 1 || z >= 1) {
            __cil_tmp_x = x;
            __cil_tmp_y = y;
            __cil_tmp_z = z;
            __cil_tmp_w = w;
            if (y >= 1) {
                x = __VERIFIER_nondet_int();
                y = __VERIFIER_nondet_int();
                if (!(x >= 2 * __cil_tmp_x - __cil_tmp_y && y >= 0 && y <= __cil_tmp_y - 1))
                    break;
                } else {
                    x = __VERIFIER_nondet_int();
                    y = __VERIFIER_nondet_int();
                    z = __VERIFIER_nondet_int();
                    w = __VERIFIER_nondet_int();
                if (!(__cil_tmp_x - __cil_tmp_y <= x + 2 * y && x + 2 * y <= __cil_tmp_x && __cil_tmp_y + 1 <= y && y <= x && z <= __cil_tmp_z + __cil_tmp_w && w <= __cil_tmp_w - y))
                    break;
            }
        }
    }
    return 0;
}
