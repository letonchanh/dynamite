public class Decreasing_with_increasing_bound {
    public static void vtrace1(int x, int y) {
        System.out.println("vtrace1: " + x + ", " + y);
    }

    public static void main (String[] args) {
        int x = Nondet.getInt();
        int y = Nondet.getInt();
        mainQ(x, y);
    }

    public static void mainQ(int x, int y) {
        while (x >= y) {
            vtrace1(x, y);
            x = x - 1;
            y = y + 1;
        }
    }
}
