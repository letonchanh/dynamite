public class Nonterm1 {

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
        // 1. -x - y <= -10
        // 2. -x <= 0

        // TERM BASE:
        // 1. x <= -1

        // TERM REC:
        // 1. y <= -4
        // 2. -x <= 0
        int x0, y0, x1, y1;
        int counter = 0;

        // while (x >= 0) {
        //     x = x + y;
        //     y = y + 1;
        // }

        while (x >= 0) {
            if (counter > bnd) break;
            else
                counter++;
            vtrace1(x, y);
            // 1. -x - y <= -3
            // 2. -x <= 0

            x0 = x;
            y0 = y;
            x1 = x0 + y0;
            y1 = y0 + 1;
            x = x1;
            y = y1;
            vtrace3(x0, y0, x1, y1);
            // 1. y0 - y1 + 1 == 0
            // 2. x0 - x1 + y1 - 1 == 0
            // 3. -x0 <= 0

            // RECURRENT SET:
            // -x0 - y0 <= -3 /\ -x0 <= 0
            // /\ y0 - y1 + 1 == 0 /\ x0 - x1 + y1 - 1 == 0 /\ -x0 <= 0
            // -> -x1 - y1 <= -3 /\ -x1 <= 0 (Invalid)

            // UNSAT(LHS /\ !RHS)
            // LHS: -x0 - y0 <= -3 /\ -x0 <= 0 /\ y0 - y1 + 1 == 0 /\ x0 - x1 + y1 - 1 == 0 /\ -x0 <= 0
            // RHS: -x1 - y1 <= -3 /\ -x1 <= 0
            // Not an inv: -x1 - y1 <= -3
            // 1. Generate new test cases for the case x + y < 3
            // 2. Eliminate traces where -x1 - y1 > -3 (which implies y0 < -1)
            // (Move the eliminated traces to MAYBE)
            // ==> x>=0 /\ x+y>=3 /\ y>=-1
        }
        if (counter <= bnd) {
            vtrace2(x, y);
            // TERM BASE:
            // 1. x <= -1

            // TERM REC:
            // 1. x <= -1
            // 2. -x + y <= 1
        }
    }
}
