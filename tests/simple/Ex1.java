public class Ex1 {
    public static void vtrace1( int x, int y) {}
    public static void vtrace2(int x, int y) {}
    public static void vtrace3(int x, int y) {}
    public static void vtrace4(int x0, int y0, int x1, int y1) {}

    public static void main (String[] args) {}

    public static void mainQ(int x, int y) {
        // assert (bnd > 0);
        vtrace1(x, y);
        int bnd = 500;
        int counter = 0;
        while (x >= 0) {
            if (counter >= bnd)
                break;
            else
                counter++;
            vtrace2(x, y);

            int x0 = x;
            int y0 = y;

            x = x + y;
            y = y + 1;

            int x1 = x;
            int y1 = y;
            vtrace4(x0, y0, x1, y1);
        }
        if (counter < bnd)
            vtrace3(x, y);
    }
}

/*
  [
  ZInvs([
  x*-1 <= -2,

  Not(Or(And(x*-1 + y*-1 <= -5, y <= -3), And(x*-1 <= 0, y <= -1))),
  //Not(And(x >= 0, y <= -1))

  Not(Or(And(And(y <= -5, x + y <= 6), x*-1 + y*-1 <= -5), And(And(And(x*-1 <= 0, x + y <= 6), x*-1 + y <= -4), y <= -3))),
  //Not(And(x >= 0, x + y <= 6, x*-1 + y <= -4, y <= -3))

  Not(Or(And(And(y <= -2, x + y <= 4), x*-1 + y*-1 <= -2), And(And(x*-1 <= 0, x + y <= 4), y <= -2))),
  //Not(And(x >= 0, x + y <= 4, y <= -2))

  x*-1 + y*-1 <= -2]),

  ZInvs([x*-1 <= -2, Not(Or(And(x*-1 + y*-1 <= -5, y <= -3),
  And(x*-1 <= 0, y <= -1))), Not(Or(And(And(y <= -5, x + y <= 6), x*-1 + y*-1 <= -5),
  And(And(And(x*-1 <= 0, x + y <= 6), x*-1 + y <= -4),
  y <= -3))), Not(Or(And(And(y <= -2, x + y <= 4), x*-1 + y*-1 <= -2),
  And(And(x*-1 <= 0, x + y <= 4), y <= -2))), x*-1 + y*-1 <= -2])]

  ZInvs([
  x*-1 <= -1,
  Not(Or(And(y <= -2, x*-1 + y*-1 <= -9), And(And(And(x*-1 <= 0, x + y <= 10), x*-1 + y <= -4), y <= -3))),
  x*-1 + y*-1 <= -9
  ])

  ZInvs([
  x*-1 + y*-1 <= -8,
  x*-1 <= -2,
  y*-1 <= 9,
  Not(Or(And(And(x*-1 + y*-1 <= -8, y*-1 <= 9), y <= -2), And(And(And(y <= -1, x*-1 <= 0), y*-1 <= 9), x*-1 + y*-1 <= 7)))
  ])
  Repeat(Then(OrElse('split-clause', 'nnf'), 'propagate-ineqs', 'ctx-solver-simplify'))
 */