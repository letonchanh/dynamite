public class Decreasing_non_bound {
    public static void vtrace1(int x) {
        System.out.println("vtrace1: " + x);
    }

    public static void vtrace2(int x) {
        System.out.println("vtrace2: " + x);
    }

    public static void main (String[] args) {
        int x = Nondet.getInt();
        mainQ(x);
    }

    public static void mainQ(int x) {
        while (Nondet.getBool()) {
            vtrace1(x);
            x = x - 1;
        }
        vtrace2(x);
    }
}
