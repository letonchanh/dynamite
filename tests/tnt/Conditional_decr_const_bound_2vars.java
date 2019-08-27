public class Conditional_decr_const_bound_2vars {
    public static void vtrace0(int x, int y) {
        System.out.println("vtrace0: " + x + ", " + y);
    }

    public static void vtrace1(int x, int y) {
        System.out.println("vtrace1: " + x + ", " + y);
    }

    public static void vtrace2(int x, int y) {
        System.out.println("vtrace2: " + x + ", " + y);
    }

    public static void main (String[] args) {
        int bnd = Integer.parseInt(args[0]);
        int x = Nondet.getInt();
        int y = Nondet.getInt();
        mainQ(bnd, x, y);
    }

    public static void mainQ(int bnd, int x, int y) {
        vtrace0(x, y);
        int counter = 0;
        while (x >= 0) {
            if (counter > bnd) break;
            else
                counter++;
            vtrace1(x, y);
            x = x + y;
        }
        if (counter <= bnd)
            vtrace2(x, y);
    }
}
