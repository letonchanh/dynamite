import java.util.Random;

public class Nondet {
    public static Random rand = new Random();
    private static int MIN = -100;
    private static int MAX = 100;
    private static double PROB = 0.95;

    public static int getInt() {
        return rand.nextInt(MAX - MIN) + MIN;
    }

    public static boolean getBool() {
        return rand.nextInt(100) <= (PROB * 100);
    }

    public static double getDouble() {
        return MIN + (MAX - MIN) * rand.nextDouble();
    }
}
