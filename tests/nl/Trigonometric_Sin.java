import java.lang.Math; 

public class Trigonometric_Sin {
    public static void vtrace0(int a, int x, double y) {
        System.out.println("vtrace0: " + a + ", " + x + ", " + y);
    }

    public static void vtrace1(int a, int x, double y) {
        System.out.println("vtrace1: " + a + ", " + x + ", " + y);
    }

    public static void vtrace2(int a, int x, double y) {
        System.out.println("vtrace2: " + a + ", " + x + ", " + y);
    }

    public static void main (String[] args) {
        int bnd = Integer.parseInt(args[0]);
        int a = Nondet.getInt();
        int x = Nondet.getInt();
        double y = Nondet.getDouble();
        mainQ(bnd, a, x, y);
    }

    public static void mainQ(int bnd, int a, int x, double y) {
        vtrace0(a, x, y);
        int counter = 0;
        while (y < 42) {
            if (counter > bnd) break;
            else
                counter++;
            vtrace1(a, x, y);
            y = a * Math.sin(x);
            x = x + 1;
            a = a + 1;
        }
        if (counter <= bnd)
            vtrace2(a, x, y);
    }
}
