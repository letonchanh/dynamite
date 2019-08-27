public class Decreasing_const_bound_nonterm {
    public static void vtrace1(int x) {
        System.out.println("vtrace1: " + x);
    }

    public static void vtrace2(int x) {
        System.out.println("vtrace2: " + x);
    }

    public static void main (String[] args) {
        int bnd = Integer.parseInt(args[0]);
        int x = Nondet.getInt();
        mainQ(bnd, x);
    }

    public static void mainQ(int bnd, int x) {
        while (x >= 0) {
            if (bnd <= 0) break;
            else
                bnd = bnd - 1;
            vtrace1(x);
            x = x + 1;
        }
        if (bnd > 0)
            vtrace2(x);
    }
}
