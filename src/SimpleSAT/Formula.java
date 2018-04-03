package SimpleSAT;

import java.io.FileNotFoundException;
import java.lang.reflect.Array;
import java.math.BigInteger;
import java.util.*;
import java.io.BufferedInputStream;
import java.io.FileInputStream;

import static java.lang.Math.abs;

public class Formula {

    private ArrayList<Literal> literalList;
    private ArrayList<Clause> clauseList;
    private ArrayList<Literal> formulaSolution;

    private int numVariables, numClauses, numAssignedVariables, selectedLiteralIndex;

    private boolean isFormulaSAT = false;


    Formula(final String fileName) {
        importCNF(fileName);
        formulaSolution = new ArrayList<>(numVariables);
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
                System.out.println("Clause: " + clauseList.get(clause));
                start = i + 1;
                end = start;
                clause++;
            } else {
                end++;
            }
        }
        System.out.println("Literals: " + literalList);

        sc.close();
    }

    void solve() {
        ArrayList<Clause> dynamicClauseArray = new ArrayList<>(clauseList.size());
        ArrayList<Literal> assignedLiterals = new ArrayList<>(1);

        // Copy all clauses from clauseList to the dynamicClauseArray that will be modified in DPLL.
        dynamicClauseArray.addAll(clauseList);

        DPLL(dynamicClauseArray, assignedLiterals);
    }

    private boolean DPLL (ArrayList<Clause> dynamicClauseArray, ArrayList<Literal> assignedLiterals) {
        int nextLiteral;
        Literal leftLiteral;
        Literal rightLiteral;
        ArrayList<Literal> leftLiteralBranch = new ArrayList<>(1);
        ArrayList<Literal> rightLiteralBranch = new ArrayList<>(1);
        ArrayList<Clause> leftClauseBranch = new ArrayList<>(1);
        ArrayList<Clause> rightClauseBranch = new ArrayList<>(1);

        // Exit all recursions if the isFormulaSAT flag is set to true.  This is set when the whole dynamicClauseArray
        // is determined to be satisfied.
        if (isFormulaSAT) {
            return true;
        }

        // Copy all relevant data structures to new structures to pass to the next iteration of DPLL.
        copyDataStructures(assignedLiterals, dynamicClauseArray, leftLiteralBranch, rightLiteralBranch, leftClauseBranch, rightClauseBranch);

        // Pick a new literal to branch on
        nextLiteral = pickLiteral(assignedLiterals);

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
        if (assignedLiterals.size() == literalList.size()) {
            return false;
        }

        // If nextLiteral is -1, that means all literals have been used, so this condition may not be necessary
        if (nextLiteral != -1) {
            // Set up the parameters for the left branch with the new literal and a false value.
            leftLiteral = new Literal(nextLiteral, false);
            leftLiteralBranch.add(leftLiteral);
            assignLiteralToClauses(leftClauseBranch, leftLiteral);

            // Set up the parameters for the right branch with the new literal and a true value.
            rightLiteral = new Literal(nextLiteral, true);
            rightLiteralBranch.add(rightLiteral);
            assignLiteralToClauses(rightClauseBranch, rightLiteral);

            // Make the recursive call
            return (DPLL(leftClauseBranch, leftLiteralBranch) || DPLL(rightClauseBranch, rightLiteralBranch));
        }

        return false;
    }

    // This is a dumb function to pick a new literal to branch on.
    // assignedLiterals is an ArrayList of literals that have already been picked.
    // pickLiteral simply picks a value that has not been picked.
    // If all literals have been picked, it returns -1 to let the calling function know.
    private int pickLiteral(ArrayList<Literal> assignedLiterals) {
        for (Literal literal : literalList) {
            if (!assignedLiterals.contains(literal)) {
                return literal.getLiteral();
            }
        }

        return -1;
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
    }

    private void copyDataStructures(ArrayList<Literal> assignedLiterals, ArrayList<Clause> dynamicClauseArray, ArrayList<Literal> leftLiteralBranch, ArrayList<Literal> rightLiteralBranch, ArrayList<Clause> leftClauseBranch, ArrayList<Clause> rightClauseBranch) {
        // Copy the incoming clause list to a new list that will be passed to the left and right recursive calls.
        // Prune out satisfied clauses while doing this.
        for (Clause clause : dynamicClauseArray) {
            if (!clause.isSAT()) {
                leftClauseBranch.add(new Clause(clause));
                rightClauseBranch.add(new Clause(clause));
            }

        }

        // Copy the assigned literals to two new lists that will be used in the recursive calls
        leftLiteralBranch.addAll(assignedLiterals);
        rightLiteralBranch.addAll(assignedLiterals);

        /*for (int i = 0; i < assignedLiterals.size(); i++) {
            leftLiteralBranch.add(new Literal(assignedLiterals.get(i)));
            rightLiteralBranch.add(new Literal(assignedLiterals.get(i)));
        }*/
    }

    private void assignValueToClauses(Literal newLiteral) {
        for (int i = 0; i < numClauses; i++) {
            clauseList.get(i).assign(newLiteral);
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