import java.util.Random;

public class Cook_cacm11_fig1 {
    public static Random rand = new Random();
    private static int MIN = 1;
    private static int MAX = 100;

    public static int nondet() {
        return rand.nextInt(MAX - MIN) + MIN; 
    }

    public static void vtrace1(int x, int y) {
        System.out.println(x + ", " + y);
    }

    public static void main (String[] args) {
        int x = nondet();
        int y = nondet();
        mainQ(x, y);
    }

    public static void mainQ(int x, int y) {
        while (x>0 && y>0) {
            vtrace1(x, y);

            if (rand.nextBoolean()) {
                x = x - 1;
                y = y + 1;
            } else {
                y = y - 1;
            }
        }
    }
}
