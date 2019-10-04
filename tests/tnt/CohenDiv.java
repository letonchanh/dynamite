public class CohenDiv {
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

    public static void main (String[] args) {
        int bnd = Integer.parseInt(args[0]);
        int x = Nondet.getInt();
        int y = Nondet.getInt();
        mainQ(bnd, x, y);
    }

    public static int mainQ(int bnd, int x, int y) {
        // assert(y >= 1);

        int q=0;
        int r=x;
        int a=0;
        int b=0;

        vtrace0(q,r,a,b,x,y);

        int counter1 = 0;
        while(true) {
            if (counter1 > bnd) break;
            else
                counter1++;
            vtrace1(q,r,a,b,x,y);

            if(!(r >= y)) break;
            a = 1;
            b = y;

            int counter2 = 0;
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
        }

        if (counter1 <= bnd) {
            vtrace2(q,r,a,b,x,y);
        }
        return q;
    }
}
