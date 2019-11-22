public class Mysore {
    public static void vtrace1( int x, int c) {}
    public static void vtrace2(int x, int c) {}
    public static void vtrace3(int x, int c) {}
    public static void vtrace4(int x0, int c0, int x1, int c1) {}

    public static void main (String[] args) {}

    public static void whileQ(int x, int c) {
        vtrace1(x, c);
        int bnd = 500;
        int counter = 0;
        while (x + c >= 0) {
            if (counter >= bnd)
                break;
            else
                counter++;
            vtrace2(x, c);

            int x0 = x;
            int c0 = c;

            x = x - c;
            c = c - 1;

            int x1 = x;
            int c1 = c;
            vtrace4(x0, c0, x1, c1);
        }
        if (counter < bnd)
            vtrace3(x, c);
    }

    public static void mainQ(int x, int c) {
        if(!(-65535<=x && x<=65535)) return;
        if(!(-65535<=c && c<=65535)) return;
        if (c < 0) {
            whileQ(x, c);
        }
    }
}

// if (c < 0) {
//     while (x + c >= 0) {
//         x = x - c;
//         c = c - 1;
//     }
// }
