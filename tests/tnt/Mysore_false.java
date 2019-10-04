public class Mysore_false {

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
        int c = Nondet.getInt();
        int x = Nondet.getInt();
        mainQ(bnd, c, x);
    }

    public static void mainQ(int bnd, int c, int x) {
        vtrace0(c, x);

        int c0, c1, x0, x1;
        int counter = 0;

        // if (c < 0) {
        //     while (x + c >= 0) {
        //         x = x - c;
        //         c = c - 1;
        //     }
        // }

        if (c < 0) {

            while (x + c >= 0) {
                if (counter > bnd) break;
                else
                    counter++;
                vtrace1(c, x);
                // 1. -c - x <= 0
                // 2. c <= -1

                c0 = c;
                x0 = x;
                x1 = x0 - c0;
                c1 = c0 - 1;
                x = x1;
                c = c1;

                vtrace3(c0, x0, c1, x1);
            }
            if (counter <= bnd) {
                vtrace2(c, x);
            }
        }
    }
}
