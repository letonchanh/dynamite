public class CohenDiv_inner_SSA {
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

        int q=0;
        int r=x;
        int a=0;
        int b=0;

        int q0, q1, r0, r1, a0, a1, b0, b1, x0, x1, y0, y1;

        int counter1 = 0;
        int counter2 = 0;
        while(true) {
            if (counter1 > bnd) break;
            else
                counter1++;

            if(!(r >= y)) break;
            a = 1;
            b = y;

            vtrace0(q,r,a,b,x,y);
            // MAYLOOP
            // 1. q*y + r - x == 0
            // 2. b - y == 0
            // 3. a - 1 == 0
            // 4. -q <= 0
            // 5. a - x <= -10
            // 6. b <= -2

            // TERM REC
            // 1. a - 1 == 0
            // 2. b - y == 0
            // 3. b - x <= 0
            // 4. -q <= 0
            // 5. -r + y <= 0

            // TERM BASE

            while (r >= 2*b) {
                //assert(q*y + r == x);
                //assert(a*y == b);
                if (counter2 > bnd) break;
                else
                    counter2++;
                vtrace1(q,r,a,b,x,y);
                // 1. a*b*y - (b*b) == 0
                // 2. r - x == 0
                // 3. q == 0
                // 4. y <= -2
                // 5. b <= 0

                q0 = q;
                r0 = r;
                a0 = a;
                b0 = b;
                x0 = x;
                y0 = y;

                //vtrace3(q,r,a,b,x,y);
                //if(!(r >= 2*b)) break;

                a = 2*a;
                b = 2*b;

                q1 = q;
                r1 = r;
                a1 = a;
                b1 = b;
                x1 = x;
                y1 = y;

                vtrace4(q0,r0,a0,b0,x0,y0,q1,r1,a1,b1,x1,y1);
            }

            if (counter2 <= bnd) {
                vtrace2(q,r,a,b,x,y);
                // 1. a*y - b == 0
                // 2. -x + y <= 0
                // 3. -a - q <= -2
                // 4. -r + y <= 0
                // 5. b - r <= 0
                // 6. -a - y <= -2
                // 7. -a <= -1
                // 8. -q <= 0
            }


            r=r-b;
            q=q+a;

            q1 = q;
        }

        return q;
    }
}
