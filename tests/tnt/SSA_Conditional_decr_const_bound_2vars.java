public class SSA_Conditional_decr_const_bound_2vars {

    public static void vtrace0(int x, int y) {
        System.out.println("vtrace0: " + x + ", " + y);
    }

    public static void vtrace1(int x, int y) {
        System.out.println("vtrace1: " + x + ", " + y);
    }

    public static void vtrace2(int x, int y) {
        System.out.println("vtrace2: " + x + ", " + y);
    }

    public static void vtrace3(int x0, int y0, int x1, int y1) {
        System.out.println("vtrace3: " + x0 + ", " + y0 + ", " + x1 + ", " + y1);
    }

    public static void main (String[] args) {
        int bnd = Integer.parseInt(args[0]);
        int x = Nondet.getInt();
        int y = Nondet.getInt();
        mainQ(bnd, x, y);
    }

    public static void mainQ(int bnd, int x, int y) {
        vtrace0(x, y);
        // MAYLOOP:
        // 1. -x <= -1
        // 2. -y <= -5

        // TERM BASE:
        // 1. x <= -2

        // TERM REC:
        // 1. y <= -1
        // 2. -x <= -3
        int x0, y0, x1, y1;
        int counter = 0;

        // while (x >= 0) {
        //     x = x + y;
        // }

        while (x >= 0) {
            if (counter > bnd) break;
            else
                counter++;
            vtrace1(x, y);
            // 1. -y <= -5
            // 2. -x <= -1

            x0 = x;
            y0 = y;
            x1 = x0 + y0;
            y1 = y0;
            x = x1;
            y = y1;
            vtrace3(x0, y0, x1, y1);
            // 1. y0 - y1 == 0
            // 2. x0 - x1 + y1 == 0
            // 3. -x0 <= 0

            // RECURRENT SET:
            // x0>=1 & y0>=5 & y0-y1=0 & x0-x1+y1=0 -> x1>=1 & y1>=5
        }
        if (counter <= bnd) {
            vtrace2(x, y);
            // TERM BASE:
            // 1. x <= -2

            // TERM REC:
        }
    }
}
