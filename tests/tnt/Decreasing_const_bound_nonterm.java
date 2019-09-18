public class Decreasing_const_bound_nonterm {
    public static void vtrace0(int x) {
        System.out.println("vtrace0: " + x);
    }

    public static void vtrace1(int x) {
        System.out.println("vtrace1: " + x);
    }

    public static void vtrace3(int x0, int x) {
        System.out.println("vtrace3: " + x0 + ", " + x);
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
        vtrace0(x);
        int counter = 0;
        while (x >= 0) {
            if (counter > bnd) break;
            else
                counter++;
            vtrace1(x);
            int x0 = x;
            x = x + 1;
            vtrace3(x0, x);
        }
        if (counter <= bnd)
            vtrace2(x);
    }
}
