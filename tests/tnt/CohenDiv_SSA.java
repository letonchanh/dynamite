public class CohenDiv_SSA {
    public static void vtrace0(int q, int r, int a, int b, int x, int y) {
        System.out.println("vtrace0: " + q + ", " + r + ", " + a + ", " + b + ", " + x + ", " + y);
    }
    public static void vtrace1(int q, int r, int a, int b, int x, int y) {
        System.out.println("vtrace1: " + q + ", " + r + ", " + a + ", " + b + ", " + x + ", " + y);
    }
    public static void vtrace2(int q, int r, int a, int b, int x, int y) {
        System.out.println("vtrace2: " + q + ", " + r + ", " + a + ", " + b + ", " + x + ", " + y);
    }
    public static void vtrace3(int q, int r, int a, int b, int x, int y) {
        System.out.println("vtrace3: " + q + ", " + r + ", " + a + ", " + b + ", " + x + ", " + y);
    }
    public static void vtrace4(int q0, int r0, int a0, int b0, int x0, int y0, int q1, int r1, int a1, int b1, int x1, int y1) {
        System.out.println("vtrace4: " + q0 + ", " + r0 + ", " + a0 + ", " + b0 + ", " + x0 + ", " + y0 + ", " + q1 + ", " + r1 + ", " + a1 + ", " + b1 + ", " + x1 + ", " + y1);
    }
    public static void vtrace5(int x0, int x1) {
        System.out.println("vtrace5: " + x0 + ", " + x1);
    }

    public static void main (String[] args) {
        int bnd = Integer.parseInt(args[0]);
        int x = Nondet.getInt();
        int y = Nondet.getInt();
        mainQ(bnd, x, y);
    }

    public static int mainQ(int bnd, int x, int y) {
        // assert(y >= 1);
        // assert(y <= -1);
        // assert(-x + y <= -1);

        if (!(y <= -1 && -x + y <= -1)) return -1;

        int q=0;
        int r=x;
        int a=0;
        int b=0;

        vtrace0(q,r,a,b,x,y);
        // MAYLOOP
        // 1. q == 0
        // 2. r - x == 0
        // 3. a == 0
        // 4. b == 0
        // 5. y <= -1 (*)
        // 6. -x + y <= -1 (*)

        // TERM BASE

        // TERM REC
        // 1. b == 0
        // 2. r - x == 0
        // 3. a == 0
        // 4. q == 0

        int q0, q1, r0, r1, a0, a1, b0, b1, x0, x1, y0, y1;

        int counter1 = 0;
        int counter2 = 0;
        while(true) {
            if (counter1 > bnd) break;
            else
                counter1++;
            vtrace1(q,r,a,b,x,y);

            q0 = q;
            r0 = r;
            a0 = a;
            b0 = b;
            x0 = x;
            y0 = y;

            if(!(r >= y)) break;
            a = 1;
            b = y;

            while (true) {
                //assert(q*y + r == x);
                //assert(a*y == b);
                if (counter2 > bnd) break;
                else
                    counter2++;

                //vtrace3(q,r,a,b,x,y);
                if(!(r >= 2*b)) break;

                a = 2*a;
                b = 2*b;
            }
            r=r-b;
            q=q+a;

            q1 = q;
            r1 = r;
            a1 = a;
            b1 = b;
            x1 = x;
            y1 = y;

            //vtrace5(r0, r1);

            //vtrace4(q0,r0,a0,b0,x0,y0,q1,r1,a1,b1,x1,y1);
            // 1. a1 + q0 - q1 == 0
            // 2. y0 - y1 == 0
            // 3. x0 - x1 == 0
            // 4. -a1 <= 0
            // 5. -a0 <= 0
            // 6. -r0 + y0 <= 0
            // 7. b1 - r0 <= 0
            // 8. a0 - q0 <= 0
            // 9. -x1 + y1 <= 0
            // 10. -a1 - r0 <= -2

            // y <= -1 /\ -x + y <= -1
            // 1. x0 - x1 == 0
            // 2. y0 - y1 == 0
            // 3. a1 + q0 - q1 == 0
            // 4. -a0 <= 0
            // 5. -r0 + y0 <= 0
            // 6. -a1 <= 0
            // 7. b1 - r0 <= 0
            // 8. a0 - q0 <= 0
            // 9. -x0 + y1 <= -1
            // 10. -q1 - x1 <= -8
            // 11. -q1 - r0 <= -5
            // 12. -a1 - r0 <= -2
        }

        if (counter1 <= bnd && counter2 <= bnd) {
            vtrace2(q,r,a,b,x,y);
            // 1. r - y <= -1
            // 2. a - q <= 0
            // 3. -a <= 0
            // 4. r - x <= 0
        }
        return q;
    }
}
