package SimpleSAT;

public final class Solver {

    public static void main(final String[] args) {

        System.out.println("Loading file");

        final Formula formula = new Formula(args[0]);

        long startTime = System.nanoTime();

        formula.solve();

        long endTime = System.nanoTime();

        long duration = (endTime - startTime);
        System.out.println("Execution time: " + duration/1000000 + "ms");
    }
}