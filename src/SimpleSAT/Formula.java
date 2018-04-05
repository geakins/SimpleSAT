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
    private long numDecisions;
    private long numConflicts;

    private boolean isFormulaSAT = false;


    Formula(final String fileName) {
        importCNF(fileName);
        formulaSolution = new ArrayList<>(numVariables);
        numDecisions = 0;
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

        DPLL(clauseList, assignedLiterals);

        if (!isFormulaSAT) {
            System.out.println("No solution found.");
            System.out.println("Decisions: " + numDecisions);
        }
    }

    private boolean DPLL (ArrayList<Clause> dynamicClauseArray, ArrayList<Literal> assignedLiterals) {
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
            return true;
        }

        if (updateUnitClauses(dynamicClauseArray, assignedLiterals) == -1) return false;

        // Keep track of how many decisions we make in the algorithm.  This is a decent metric of algorithm efficiency.
        numDecisions++;

        // Copy the Literal data structures to new structures to pass to the next iteration of DPLL.
        copyDataStructures(assignedLiterals, leftLiteralBranch, rightLiteralBranch);

        // Pick a new literal to branch on.  Returns -1 if no literals are left.
        nextLiteral = pickLiteral( assignedLiterals );

        // Check to see if the formula is SAT based on the current clause list.
        // Print solution and return if solution is found.
        if (isFormulaSAT(dynamicClauseArray)) {
            isFormulaSAT = true;
            formulaSolution = new ArrayList<>(assignedLiterals);
            System.out.println("Solution found");
            printFormulaSolution();
            return true;
        }

        // Return false if we've assigned all literals and the formula is not SAT
        if (nextLiteral == -1) {
            return false;
        } else {
            // If nextLiteral is not -1, then a literal has been picked.  Process it.
            // Set up the parameters for the left branch with the new literal and a false value.
            leftLiteral = new Literal(nextLiteral, false);
            leftLiteralBranch.add(leftLiteral);

            // Set up the parameters for the right branch with the new literal and a true value.
            rightLiteral = new Literal(nextLiteral, true);
            rightLiteralBranch.add(rightLiteral);

            // Make the recursive call
            return (DPLL(dynamicClauseArray, leftLiteralBranch) || DPLL(dynamicClauseArray, rightLiteralBranch));
        }
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
    private int updateUnitClauses(ArrayList<Clause> currentClauseList, ArrayList<Literal> currentAssignedLiterals) {
        int forcedVariable;
        int numberForced = 1;
        boolean forcedValue;
        Literal oppositeLiteral;
        Literal forcedLiteral = new Literal(0);
        ArrayList<Literal> forcedLiterals = new ArrayList<>(0);
        // removedLiterals keeps track of Literals that have already been assigned in the case that there are more than
        // one instances of a forced literal.
        ArrayList<Literal> removedLiterals = new ArrayList<>(0);

        while (numberForced != 0) {
            forcedLiterals.clear();
            removedLiterals.clear();
            forcedLiteral.setLiteral(0);
            numberForced = 0;
            for (Clause clause : currentClauseList) {
                // findImplications() returns the unassigned literal in unit clauses, or 0 otherwise.
                forcedVariable = clause.findImplications();
                if (forcedVariable != 0) {
                    // Unit clause found, assign it a value based on the literal sign
                    if (forcedVariable > 0) {
                        forcedValue = true;
                    } else {
                        forcedValue = false;
                    }

                    forcedLiteral = new Literal(Math.abs(forcedVariable), forcedValue);
                    oppositeLiteral = new Literal(forcedLiteral);
                    oppositeLiteral.complement();
                    // Add the new Literal to the forcedLiterals list.
                    forcedLiterals.add(forcedLiteral);

                    // Conflict found.  Exit here to save quite a lot of time on assigning literals.
                    if ( forcedLiterals.contains(oppositeLiteral) ) {
                        return -1;
                    }
                }
            }

            // Apply all found forced literals to the formula.
            for ( Literal literal : forcedLiterals ) {
                if (literal.getLiteral() != 0 && !removedLiterals.contains(literal)) {
                    assignLiteralToClauses(currentClauseList, literal);
                    currentAssignedLiterals.add(new Literal(literal));
                    removedLiterals.add(forcedLiteral);
                    numberForced++;
                }
            }
        }
        return 0;
    }

    // This is a dumb function to pick a new literal to branch on.
    // assignedLiterals is an ArrayList of literals that have already been picked.
    // pickLiteral simply picks a value that has not been picked.
    // If all literals have been picked, it returns -1 to let the calling function know.
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
        System.out.println("Decisions: " + numDecisions);
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