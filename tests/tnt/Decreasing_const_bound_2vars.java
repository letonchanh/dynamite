public class Decreasing_const_bound_2vars {
    public static void vtrace1(int x, int y) {
        System.out.println("vtrace1: " + x + ", " + y);
    }

    public static void vtrace2(int x, int y) {
        System.out.println("vtrace2: " + x + ", " + y);
    }

    public static void main (String[] args) {
        int x = Nondet.getInt();
        int y = Nondet.getInt();
        mainQ(x, y);
    }

    public static void mainQ(int x, int y) {
        while (x >= 0 && y >= 0) {
            vtrace1(x, y);
            x = x - 1;
            y = y - 2;
        }
        vtrace2(x, y);
    }
}
