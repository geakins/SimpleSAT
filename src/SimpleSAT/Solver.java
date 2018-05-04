package SimpleSAT;

public final class Solver {



    public static void main(final String[] args) {

        boolean DEBUG = false;
        boolean BRUTEFORCE = false;

        System.out.println("Loading file...");

        String fileLocation = args[args.length - 1];

        for ( String s : args ) {
            if ( s.equals("-b") ) {
                BRUTEFORCE = true;
            }

            if ( s.equals("-d") ) {
                DEBUG = true;
            }

        }

        final Formula formula = new Formula(fileLocation);

        if ( DEBUG ) formula.setDEBUG();

        long startTime = System.nanoTime();

        if ( BRUTEFORCE ) {
            System.out.println("Starting brute force solution...");
            formula.bruteForceSolution();
        }
        else {
            formula.solve();
        }

        long endTime = System.nanoTime();

        long duration = (endTime - startTime);
        System.out.println("Execution time: " + duration/1000000 + "ms");
    }
}