public class Ex1 {
    public static void vtrace1( int x, int y) {}
    public static void vtrace2(int x, int y) {}
    public static void vtrace3(int x, int y) {}

    public static void main (String[] args) {}

    public static void mainQ(int x, int y) {
        // assert (bnd > 0);
        vtrace1(x, y);
        int bnd = 1000;
        int counter = 0;
        while (x >= 0) {
            if (counter >= bnd)
                break;
            else
                counter++;
            vtrace2(x, y);
            x = x + y;
        }
        if (counter < bnd)
            vtrace3(x, y);
    }
}
