package SimpleSAT;

import java.io.FileNotFoundException;
import java.math.BigInteger;
import java.util.*;
import java.io.BufferedInputStream;
import java.io.FileInputStream;

import static java.lang.Math.abs;

public class Formula {

    private ArrayList<Literal> literalList;
    private ArrayList<Clause> clauseList;
    private ArrayList<Literal> formulaSolution;

    private int numVariables, numClauses;
    private long numberOfDecisions;
    private long numberOfConflicts;

    private boolean isFormulaSAT = false;

    private Random randomBoolean;


    Formula(final String fileName) {
        importCNF(fileName);
        formulaSolution = new ArrayList<>(numVariables);
        numberOfDecisions = 0;
        randomBoolean = new Random();
    }

    /**
     * Import cnf file and store clauses in
     * clauseList.
     *
     * @param fileName the file name
     */
    private void importCNF(final String fileName) {
        Scanner sc = null;
        try {
            sc = new Scanner(new BufferedInputStream(new FileInputStream(fileName)), "UTF-8");
        } catch (FileNotFoundException e) {
            System.out.println("Could not find file " + fileName + ". Try using the full path.");
            System.exit(1);
        }

        // Not a valid CNF file.
        if(sc.findWithinHorizon("p cnf", 0) == null)
            System.exit(2);

        // Reading the line: p cnf numVariables numClauses
        numVariables = sc.nextInt();
        numClauses = sc.nextInt();

        System.out.println("Number of variables: " + numVariables + " Number of clauses: " + numClauses);

        // This is the main array of clauses that keeps track of all clauses in the function.
        clauseList = new ArrayList<>(numClauses);
        // literalList contains a list of all the unique literals in the formulas.
        literalList = new ArrayList<>(numVariables);

        // Read in all clauses into a Clause object array
        int start = 0;
        int clause = 0;
        int end = 0;
        Literal literalCompare = new Literal(0);
        // Allocate the maximum amount of memory that could possibly be needed.
        int[] intBuffer = new int[numVariables*numClauses];
        System.out.println("Clauses:");
        for(int i = 0; sc.hasNextInt(); i++) {
            intBuffer[i] = sc.nextInt();

            // Check the list of literals to see if we have already added this one.
            // 0 is ignored since that is the clause terminator
            literalCompare.set(abs(intBuffer[i]));
            if (!literalList.contains(literalCompare) && literalCompare.getLiteral() != 0) {
                literalList.add(new Literal(abs(intBuffer[i])));
            }

            // Add the clause to the list if intBuffer is at the end of a line.
            if(intBuffer[i] == 0){
                clauseList.add(new Clause(Arrays.copyOfRange(intBuffer, start, end)));

                //clauseList[clause] = new Clause(Arrays.copyOfRange(intBuffer, start, end));
                System.out.println(clauseList.get(clause));
                start = i + 1;
                end = start;
                clause++;
            } else {
                end++;
            }
        }

        // Sort the master list of literals such that the most frequent ones will be selected on first.
        sortLiteralList();
        System.out.println("Literals: " + literalList);

        sc.close();
    }

    void solve() {
        ArrayList<Literal> assignedLiterals = new ArrayList<>(1);

        expandClauseList();

        DPLL( assignedLiterals );

        if (!isFormulaSAT) {
            System.out.println("No solution found.");
            System.out.println("Decisions: " + numberOfDecisions);
            System.out.println("Conflicts: " + numberOfConflicts);
        }
    }

    private int DPLL (ArrayList<Literal> assignedLiterals) {
        int nextLiteral;
        Literal leftLiteral;
        Literal rightLiteral;
        // Each branch carries its own set of assigned literals
        ArrayList<Literal> leftLiteralBranch = new ArrayList<>(1);
        ArrayList<Literal> rightLiteralBranch = new ArrayList<>(1);

        // Before entering each recursion, we need to reset the state of the clause array, since all DPLL calls
        // use the same clauseList;
        resetClauseListState();

        // Go through the list of clauses and assign values to them.
        assignLiteralListToClauseList(assignedLiterals);

        // Exit all recursions if the isFormulaSAT flag is set to true.  This is set when the whole dynamicClauseArray
        // is determined to be satisfied.
        if (isFormulaSAT) {
            return 0;
        }

        int backtrackVariable = updateUnitClauses( assignedLiterals );
        if ( backtrackVariable > 0 ) {
            return backtrackVariable;
        }

        // Copy the Literal data structures to new structures to pass to the next iteration of DPLL.
        copyDataStructures(assignedLiterals, leftLiteralBranch, rightLiteralBranch);

        // Pick a new literal to branch on.  Returns -1 if no literals are left.
        nextLiteral = pickLiteral( assignedLiterals );

        // Keep track of how many decisions we make in the algorithm.  This is a decent metric of algorithm efficiency.
        numberOfDecisions++;

        // Check to see if the formula is SAT based on the current clause list.
        // Print solution and return if solution is found.
        if (isFormulaSAT(clauseList)) {
            isFormulaSAT = true;
            formulaSolution = new ArrayList<>(assignedLiterals);
            System.out.println("Solution found");
            printFormulaSolution();
            return 0;
        }

        // Return false if we've assigned all literals and the formula is not SAT
        if (nextLiteral == -1) {
            return 0;
        } else {
            // If nextLiteral is not -1, then a literal has been picked.  Process it.
            // Set up the parameters for the left branch with the new literal and a false value.
            boolean nextValue = randomBoolean.nextBoolean();

            leftLiteral = new Literal(nextLiteral, nextValue);
            leftLiteralBranch.add(leftLiteral);

            // Make the recursive calls
            int leftBranch = DPLL( leftLiteralBranch );

            /*if ( leftBranch > 0 ) {
                return leftBranch - 1;
            }*/

            // Set up the parameters for the right branch with the new literal and a true value.
            rightLiteral = new Literal(nextLiteral, !nextValue);
            rightLiteralBranch.add(rightLiteral);
            int rightBranch = DPLL( rightLiteralBranch );


        }
        return 0;
    }

    // This method must be called before each iteration through the DPLL function, since the algorithm uses the
    // same clause list for all iterations.
    private void resetClauseListState () {
        for (Clause clause : clauseList) {
            clause.resetClause();
        }
    }

    // Takes an ArrayList of Literals that have been assigned and makes them official with the clauseList.
    private void assignLiteralListToClauseList(ArrayList<Literal> currentLiterals) {
        for (Literal literal : currentLiterals) {
            for (Clause clause : clauseList) {
                clause.assign(literal);
            }
        }
    }

    // The workhorse method of DPLL.  It takes an ArrayList of Literals that has currently been assigned and searches
    // through the clauseList for unit clauses.  It compiles a List of forced values and searches through those for
    // two things:
    // 1. A forced value
    // 2. A conflict
    // If forced values are found, they are assigned to the clause and the search starts again.
    // If a conflict is found, -1 is returned.
    private int updateUnitClauses(ArrayList<Literal> currentAssignedLiterals) {
        int forcedVariable;
        int numberForced = 1;
        boolean forcedValue;
        Literal forcedLiteral = new Literal(0);
        Literal oppositeLiteral;
        ArrayList<Literal> forcedLiterals = new ArrayList<>(0);
        // removedLiterals keeps track of Literals that have already been forced.  It speeds up the algorithm in the
        // case of multiples of the same forced literal
        ArrayList<Literal> removedLiterals = new ArrayList<>(0);

        while (numberForced != 0) {
            forcedLiteral.setLiteral(0);
            forcedLiterals.clear();
            removedLiterals.clear();
            numberForced = 0;
            for (Clause clause : clauseList) {
                // findImplications() returns the unassigned literal in unit clauses, or 0 otherwise.
                forcedVariable = clause.findImplications();
                if (forcedVariable != 0) {
                    // Unit clause found, assign it a value based on the literal sign
                    if (forcedVariable > 0) {
                        forcedValue = true;
                    } else {
                        forcedValue = false;
                    }

                    forcedLiteral = new Literal( Math.abs(forcedVariable), forcedValue );
                    forcedLiteral.setForced();
                    oppositeLiteral = new Literal( forcedLiteral );
                    oppositeLiteral.complement();
                    // Add the new Literal to the forcedLiterals list.
                    forcedLiterals.add(new Literal( forcedLiteral ));

                    // Conflict found.  Exit here to save quite a lot of time on assigning literals.
                    if ( forcedLiterals.contains(oppositeLiteral) ) {
                        numberOfConflicts++;
                        /*if (clauseList.size() < (numClauses + 5) ) {
                            addConflictClause(currentAssignedLiterals, forcedLiteral);
                            return 1;
                        }*/
                        // Returning a 1 here will abort the branch that DLL is currently on, the one that would likely
                        // result in picking a conflict literal on both subsequent branches.
                        return 1;
                    }
                }
            }

            // Apply all found forced literals to the formula.
            for ( Literal literal : forcedLiterals ) {
                if (literal.getLiteral() != 0 && !removedLiterals.contains(literal)) {
                    assignLiteralToClauses(clauseList, literal);
                    currentAssignedLiterals.add(new Literal(literal));
                    removedLiterals.add(literal);
                    numberForced++;
                }
            }
        }
        return 0;
    }

    // addConflictClause attempts to calculate a clause to add to the clauseList to earlier find conflicts and
    // terminate unsat branches sooner.
    private int addConflictClause(ArrayList<Literal> assignedLiterals, Literal conflictLiteral ) {
        Literal tempLiteral;
        int literalNumber;
        int backtrackLevels = 0;
        ArrayList<Integer> conflictClauseBuilder = new ArrayList<>(0);
        Clause conflictClause;
        ArrayList<Literal> conflictLiteralList = new ArrayList<>(0);

        literalNumber = conflictLiteral.getFullLiteral();
        for ( Clause clause : clauseList ) {
            if (clause.containsLiteral( literalNumber )) {
                conflictClauseBuilder = clause.getVariables();
                for ( int lit : conflictClauseBuilder ) {
                    tempLiteral = new Literal( Math.abs(lit) );
                    if ( lit > 0 ) {
                        tempLiteral.complement();
                    }
                    if (!conflictLiteralList.contains( tempLiteral )) {
                        conflictLiteralList.add( tempLiteral );
                    }

                }
            }
        }

        conflictClauseBuilder.clear();
        for ( Literal conflictLit : conflictLiteralList ) {
            for (Literal assLit : assignedLiterals ) {
                if ( conflictLit.getLiteral() == assLit.getLiteral() ) {
                    int tempLit = conflictLit.getLiteral();
                    if ( backtrackLevels == 0 ) {
                        for (int i = assignedLiterals.indexOf( assLit ); i < assignedLiterals.size(); i++ ) {
                            if ( !assignedLiterals.get(i).getForced() ) {
                                backtrackLevels++;
                            }
                            //backtrackLevels = assignedLiterals.size() - assignedLiterals.indexOf(assLit);
                        }
                    }
                    // Add the opposite literal of what the assigned value is.
                    if ( assLit.getValue() ) {
                        tempLit *= -1;
                    }
                    if ( !conflictClauseBuilder.contains( tempLit ) ) {
                        conflictClauseBuilder.add(tempLit);
                    }
                }
            }
        }

        // Convert the Integer List to an array, the format the Clause object takes.
        conflictClause = new Clause( IntegerListToIntArray( conflictClauseBuilder ));

        if ( !clauseList.contains( conflictClause )) {
            clauseList.add(conflictClause);
        }

        backtrackLevels -= 2;

        return backtrackLevels;
    }

    // This function simply converts an Integer List to an int[]
    private int[] IntegerListToIntArray(ArrayList<Integer> list)  {
        int[] ret = new int[list.size()];
        int i = 0;
        for (Integer e : list)
            ret[i++] = e;
        return ret;
    }

    private int expandClauseList() {
        ArrayList<Clause> newClauses = new ArrayList<>(0);
        ArrayList<Clause> clausesToRemove = new ArrayList<>(0);

        for ( Clause clause1 : clauseList ) {
            for ( Clause clause2 : clauseList ) {
                int[] newClause = checkContradiction( clause1, clause2 );
                if ( newClause != null ) {
                    if ( !clausesToRemove.contains( clause1 )) {
                        clausesToRemove.add(clause1);
                    }
                    if ( !clausesToRemove.contains( clause2 )) {
                        clausesToRemove.add(clause2);
                    }
                    Clause clauseToAdd = new Clause( newClause );
                    if ( !newClauses.contains( clauseToAdd )) {
                        newClauses.add(new Clause(newClause));
                    }
                }
            }
        }

        Iterator<Clause> iterator;

        for (Clause clauseToRemove : clausesToRemove ) {
            iterator = clauseList.iterator();
            while ( iterator.hasNext() ) {
                if (iterator.next() == clauseToRemove) {
                    iterator.remove();
                }
            }
        }

        for (Clause clauseToAdd : newClauses ) {
            clauseList.add( new Clause( clauseToAdd ));
        }

        return 0;
    }

    // Checks for two clauses to be equivalent, but with one complemented variable.
    private int[] checkContradiction( Clause clause1, Clause clause2 ) {
        if (clause1.getSize() != clause2.getSize()) {
            return null;
        }

        int listSize = clause1.getSize();
        int complementTracker = 0;
        int complementLiteral = 0;
        int matchTracker = 0;
        ArrayList<Integer> literalList1 = clause1.getVariables();
        ArrayList<Integer> literalList2 = clause2.getVariables();
        Collections.sort(literalList1, new Comparator<Integer>() {
            public int compare(Integer o1, Integer o2) {
                return Integer.compare(Math.abs(o1), Math.abs(o2));
            }
        });
        Collections.sort(literalList2, new Comparator<Integer>() {
            public int compare(Integer o1, Integer o2) {
                return Integer.compare(Math.abs(o1), Math.abs(o2));
            }
        });

        for ( int i = 0; i < listSize; i++ ) {
            if ( literalList1.get(i).equals(literalList2.get(i) )) {
                matchTracker++;
            }
            else if (literalList1.get(i) == (-1 * literalList2.get(i))) {
                complementTracker++;
                complementLiteral = literalList1.get(i);
            }
        }

        if ( complementTracker == 1 && matchTracker == (listSize - 1)) {

            ArrayList<Integer> newClause = new ArrayList<>(0);

            for ( Integer i : literalList1 ) {
                if ( Math.abs(i) != Math.abs(complementLiteral) ) {
                    newClause.add( i );
                }
            }

            return IntegerListToIntArray(newClause);
        }

        return null;
    }

    // This is a dumb function to pick a new literal to branch on.
    // assignedLiterals is an ArrayList of literals that have already been picked.
    // pickLiteral simply picks a value that has not been picked.
    // If all literals have been picked, it returns -1.
    private int pickLiteral(ArrayList<Literal> assignedLiterals) {
        Literal oppositeLiteral;
        for (Literal literal : literalList) {
            oppositeLiteral = new Literal(literal);
            oppositeLiteral.complement();
            if (!assignedLiterals.contains(literal) && !assignedLiterals.contains(oppositeLiteral)) {
                return literal.getLiteral();
            }
        }

        return -1;
    }

    private void sortLiteralList() {
        int literalCount ;
        for (Literal literal : literalList) {
            literalCount = countLiteralAppearances(clauseList, literal);
            literal.setLiteralCount(literalCount);
        }
        Collections.sort(literalList, new Comparator<Literal>() {
            @Override public int compare(Literal lit1, Literal lit2) {
                return lit2.getAppearances() - lit1.getAppearances();
            }

        });
    }

    // Counts the number of times a literal appears in a list of clauses
    private int countLiteralAppearances(ArrayList<Clause> currentClauseList, Literal literal) {
        int count = 0;
        for (Clause clause : currentClauseList) {
            if (clause.literalExists(literal)) {
                count++;
            }
        }
        return count;
    }

    private void assignLiteralToClauses(ArrayList<Clause> clauseSubList, Literal newLiteral) {
        for (Clause clause : clauseSubList) {
            clause.assign(newLiteral);
        }
    }

    private boolean isFormulaSAT(ArrayList<Clause> clauseArrayToCheck) {
        for (Clause clause : clauseArrayToCheck) {
            if (!clause.isSAT()) {
                return false;
            }
        }
        return true;
    }

    private void printFormulaSolution() {
        StringBuilder output = new StringBuilder(numVariables);
        int finalLiteral;

        for (Literal literal : formulaSolution) {
            finalLiteral = literal.getLiteral();
            // if the value assigned to a literal is negative, complement the value before outputting.
            if (!literal.getValue()) {
                finalLiteral *= -1;
            }
            output.append(finalLiteral);
            output.append(" ");
        }

        System.out.println(output.toString());
        System.out.println("Decisions: " + numberOfDecisions);
        System.out.println("Conflicts: " + numberOfConflicts);
    }

    private void copyDataStructures(ArrayList<Literal> assignedLiterals, ArrayList<Literal> leftLiteralBranch, ArrayList<Literal> rightLiteralBranch) {
        // Copy the assigned literals to two new lists that will be used in the recursive calls
        for (Literal literal : assignedLiterals) {
            leftLiteralBranch.add(new Literal(literal));
            rightLiteralBranch.add(new Literal(literal));
        }
    }

    private boolean isFormulaSAT() {
        for (int i = 0; i < numClauses; i++) {
            if (!clauseList.get(i).isSAT()) {
                return false;
            }
        }
        return true;
    }

    // In the event that we implement a clause list reduction, this method will delete all SAT clauses from a list.
    private void pruneSATClauses(ArrayList<Clause> clauseListToPrune) {
        Iterator<Clause> iterator = clauseListToPrune.iterator();

        while (iterator.hasNext()) {
            if (iterator.next().isSAT()) {
                iterator.remove();
            }
        }
    }

    public void bruteForceSATSolver() {
        int i, j;
        BigInteger totalPossibilities;

        totalPossibilities = new BigInteger("2");
        totalPossibilities = totalPossibilities.pow(numVariables);

        System.out.println("Total combinations: " + totalPossibilities.toString());

        while (!isFormulaSAT()) {
            incrementLiteralListValues();
            for (i = 0; i < clauseList.size(); i++) {
                for (j = 0; j < literalList.size(); j++) {
                    if (!clauseList.get(i).isSAT()) {
                        clauseList.get(i).assignBrute(literalList.get(j));
                    }
                }
            }
            totalPossibilities = totalPossibilities.subtract(BigInteger.ONE);
            if (totalPossibilities.equals(BigInteger.ZERO)) break;
        }
        if (isFormulaSAT()) {
            printBruteForceSolution();
        }
        else {
            System.out.println("No solution!");
        }
    }

    private void incrementLiteralListValues() {
        boolean carry = true;
        for (int i = (literalList.size() - 1); i >= 0; i--) {
            if (carry) {
                if (!literalList.get(i).getValue()) {
                    literalList.get(i).assign(true);
                    carry = false;
                }
                else {
                    literalList.get(i).assign(false);
                    carry = true;
                }
            }
        }
    }

    private void printBruteForceSolution() {
        StringBuilder output = new StringBuilder(numVariables);
        int finalLiteral;

        for (Literal literal : literalList) {
            finalLiteral = literal.getLiteral();
            if (!literal.getValue()) {
                finalLiteral *= -1;
            }
            output.append(finalLiteral);
            output.append(" ");
        }

        System.out.println(output.toString());

    }
}