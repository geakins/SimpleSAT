package SimpleSAT;

public final class Solver {

    public static void main(final String[] args) {
        long startTime = System.nanoTime();

        System.out.println("Loading file");

        final Formula formula = new Formula(args[0]);

        //formula.bruteForceSATSolver();
        formula.solve();
        //System.out.println(formula.isFormulaSatisfiable());

        long endTime = System.nanoTime();
        long duration = (endTime - startTime);
        System.out.println("Execution time: " + duration/1000000);
    }
}