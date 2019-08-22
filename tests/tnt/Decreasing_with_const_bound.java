public class Decreasing_with_bound {
    public static void vtrace1(int x) {
        System.out.println("vtrace1: " + x);
    }

    public static void main (String[] args) {
        int x = Nondet.getInt();
        mainQ(x);
    }

    public static void mainQ(int x) {
        while (x >= -7) {
            vtrace1(x);
            x = x - 1;
        }
    }
}
