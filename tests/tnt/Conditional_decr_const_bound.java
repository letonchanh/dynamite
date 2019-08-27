public class Conditional_decr_const_bound {
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
        while (x >= 0) {
            if (bnd <= 0) break;
            else
                bnd = bnd - 1;
            vtrace1(x, y);
            x = x + y;
        }
        if (bnd > 0)
            vtrace2(x, y);
    }
}
