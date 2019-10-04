public class Alternative {

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
        int b = Nondet.getInt();
        int x = Nondet.getInt();
        mainQ(bnd, b, x);
    }

    public static void mainQ(int bnd, int b, int x) {
        vtrace0(b, x);
        // TERM BASE:
        // 1. x <= -1

        // TERM REC:
        // 1. -x <= 0
        // 2. x <= 1

        // MAYLOOP:
        // 1. -x <= 0

        int b0, b1, x0, x1;
        int counter = 0;

        // while (x >= 0):
        //     b = b+1
        //     if (b % 2 == 0):
        //       x = x + 3
        //     else:
        //       x = x - 2

        while (x >= 0) {
            if (counter > bnd) break;
            else
                counter++;
            vtrace1(b, x);
            // 1. -x <= 0

            b0 = b;
            x0 = x;
            b1 = b0 + 1;
            if (b1 % 2 == 0) {
                x1 = x0 + 3;
            } else {
                x1 = x0 - 2;
            }
            b = b1;
            x = x1;

            vtrace3(b0, x0, b1, x1);
        }
        if (counter <= bnd) {
            vtrace2(b, x);
        }
    }
}
