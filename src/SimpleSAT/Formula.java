package SimpleSAT;

import java.io.FileNotFoundException;
import java.math.BigInteger;
import java.util.*;
import java.io.BufferedInputStream;
import java.io.FileInputStream;

import static java.lang.Integer.MAX_VALUE;
import static java.lang.Math.abs;

public class Formula {

    private ArrayList<Literal> literalList;
    private ArrayList<Clause> clauseList;
    private ArrayList<Literal> formulaSolution;
    private ArrayList<Integer> conflictLiterals;
    private ArrayList<Integer> backtrackLiterals;

    private int numVariables, numClauses;
    private long numberOfDecisions;
    private long numberOfConflicts;

    private boolean isFormulaSAT = false;
    private boolean DEBUG = false;

    Formula(final String fileName) {
        importCNF(fileName);
        formulaSolution = new ArrayList<>(numVariables);
        conflictLiterals = new ArrayList<>(0);
        backtrackLiterals = new ArrayList<>(0);
        numberOfDecisions = 0;
        numberOfConflicts = 0;
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
        if ( DEBUG ) System.out.println("Clauses:");
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
                if ( DEBUG ) System.out.println(clauseList.get(clause));
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

        if ( expandClauseList() == -1 ) {
            System.out.println("RESULT: UNSAT");
            System.out.println("Decisions: " + numberOfDecisions);
            System.out.println("Conflicts: " + numberOfConflicts);
            return;
        }

        numberOfDecisions = 0;
        numberOfConflicts = 0;
        DPLL( clauseList, assignedLiterals, literalList );

        if (!isFormulaSAT) {
            System.out.println("RESULT: UNSAT");
            System.out.println("Decisions: " + numberOfDecisions);
            System.out.println("Conflicts: " + numberOfConflicts);
        }
        else {
            //formulaSolution = new ArrayList<>(assignedLiterals);
            printFormulaSolution();
        }
    }

    private int DPLL (ArrayList<Clause> dpllClauseList, ArrayList<Literal> assignedLiterals, ArrayList<Literal> allLiterals) {
        int nextLiteral;
        Literal leftLiteral;
        Literal rightLiteral;
        // Each branch carries its own set of assigned literals
        ArrayList<Literal> leftLiteralBranch = new ArrayList<>();
        ArrayList<Literal> rightLiteralBranch = new ArrayList<>();

        // Before entering each recursion, we need to reset the state of the clause array, since all DPLL calls
        // use the same clauseList;
        resetClauseListState( dpllClauseList );

        // Go through the list of clauses and assign values to them.
        assignLiteralListToClauseList( dpllClauseList, assignedLiterals );

        // Exit all recursions if the isFormulaSAT flag is set to true.  This is set when the whole dynamicClauseArray
        // is determined to be satisfied.
        if (isFormulaSAT) {
            return 0;
        }

        int backtrackLiteral = updateUnitClauses( dpllClauseList, assignedLiterals );
        if ( backtrackLiteral > 0 || backtrackLiteral == -2 ) {
            return backtrackLiteral;
        }

        // Copy the Literal data structures to new structures to pass to the next iteration of DPLL.
        copyDataStructures(assignedLiterals, leftLiteralBranch, rightLiteralBranch);

        // Pick a new literal to branch on.  Returns -1 if no literals are left.
        nextLiteral = pickLiteral( assignedLiterals, allLiterals );

        // Keep track of how many decisions we make in the algorithm.  This is a decent metric of algorithm efficiency.
        numberOfDecisions++;

        // Check to see if the formula is SAT based on the current clause list.
        // Print solution and return if solution is found.
        if (isFormulaSAT( dpllClauseList )) {
            isFormulaSAT = true;
            if ( allLiterals.size() == literalList.size() ) {
                recordFormulaSolution(assignedLiterals);
            }
            return 0;
        }

        // Return false if we've assigned all literals and the formula is not SAT
        if (nextLiteral == -1) {
            return 0;
        } else {
            // If nextLiteral is not -1, then a literal has been picked.  Process it.
            // Set up the parameters for the left branch with the new literal and a false value.
            boolean nextValue = false;

            leftLiteral = new Literal( nextLiteral, nextValue );
            leftLiteralBranch.add( leftLiteral );

            // Make the recursive calls
            if ( DEBUG ) System.out.println("Left on " + nextLiteral);
            int leftBranch = DPLL( dpllClauseList, leftLiteralBranch, allLiterals );

            if ( leftBranch > 0 && leftBranch != nextLiteral ) {
                return leftBranch;
            }

            //System.out.println("Right on " + nextLiteral );
            // Set up the parameters for the right branch with the new literal and a true value.
            if ( DEBUG ) System.out.println("Right on " + nextLiteral );
            rightLiteral = new Literal( nextLiteral, !nextValue );
            rightLiteral.setRightBranch();
            rightLiteralBranch.add( rightLiteral );
            int rightBranch = DPLL( dpllClauseList, rightLiteralBranch, allLiterals );


        }
        return 0;
    }

    // The workhorse method of DPLL.  It takes an ArrayList of Literals that has currently been assigned and searches
    // through the clauseList for unit clauses.  It compiles a List of forced values and searches through those for
    // two things:
    // 1. A forced value
    // 2. A conflict
    // If forced values are found, they are assigned to the clause and the search starts again.
    // If a conflict is found, -1 is returned.
    private int updateUnitClauses(ArrayList<Clause> dpllClauseList, ArrayList<Literal> currentAssignedLiterals) {
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
            for (Clause clause : dpllClauseList) {
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
                        //System.out.println("Conflict");
                        if (dpllClauseList.size() < ( numClauses * 1.5 )) {
                            if (conflictLiterals.contains( forcedLiteral.getLiteral() )) {
                                return -2;
                            }
                            // Based on the literal being forced (the conflict literal), generate a conflict clause.
                            int x = addConflictClause(dpllClauseList, currentAssignedLiterals, forcedLiteral);
                            conflictLiterals.add( forcedLiteral.getLiteral() );
                            if (backtrackLiterals.contains( x )) {
                                break;
                            }

                            backtrackLiterals.add( x );

                            if ( x > 0 || x == -2 ) return x;
                            else break;
                        }
                        // Returning a -2 indicated that DPLL should abort the current branch that it is on, but the
                        // maximum number of conflict clauses has been reached.
                        return -2;
                    }
                }
            }

            // Apply all found forced literals to the formula.
            for ( Literal literal : forcedLiterals ) {
                if (literal.getLiteral() != 0 && !removedLiterals.contains(literal)) {
                    literal.setForced();
                    assignLiteralToClauses(dpllClauseList, literal);
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
    private int addConflictClause(ArrayList<Clause> dpllClauseList, ArrayList<Literal> assignedLiterals, Literal conflictLiteral ) {
        Literal tempLiteral;
        Literal compTempLiteral;
        int conflictLiteralNumber;
        int backtrackLiteral = MAX_VALUE;
        ArrayList<Integer> conflictClauseBuilder;
        ArrayList<Integer> conflictIntegerLiteralList = new ArrayList<>();
        ArrayList<Literal> conflictLiteralList = new ArrayList<>();
        Clause conflictClause;

        // literalNumber stores the literal in the ±x form that is stored in a Clause.
        conflictLiteralNumber = conflictLiteral.getLiteral();
        // This loop builds up a list of literals that are in the same clauses as the conflict literal.
        for ( Clause clause : dpllClauseList ) {
            if ( clause.isConflictClause() ) continue;
            // Check each clause in dpllClauseList to see if it contains the conflictLiteral
            if ( Math.abs( clause.findImplications()) == conflictLiteralNumber ) {
                //if ( clause.containsLiteral( literalNumber )) {
                conflictClauseBuilder = clause.getVariables();
                for ( int lit : conflictClauseBuilder ) {
                    if (Math.abs(lit) != conflictLiteral.getLiteral()) {
                        tempLiteral = new Literal(Math.abs(lit));
                        if (lit < 0) {
                            tempLiteral.complement();
                        }
                        compTempLiteral = new Literal(Math.abs(lit));
                        compTempLiteral.setValue(!tempLiteral.getValue());

                        if (!conflictLiteralList.contains( tempLiteral )) {
                            if (assignedLiterals.contains( tempLiteral )) {
                                conflictLiteralList.add( tempLiteral );
                                conflictIntegerLiteralList.add( lit );
                                if (assignedLiterals.indexOf( tempLiteral ) < backtrackLiteral ) {
                                    if ( !assignedLiterals.get(assignedLiterals.indexOf( tempLiteral )).isForced()) {
                                        if ( !assignedLiterals.get(assignedLiterals.indexOf( tempLiteral )).isRightBranch() ) {
                                            backtrackLiteral = assignedLiterals.indexOf( tempLiteral );
                                        }
                                    }
                                }
                            } else if (assignedLiterals.contains( compTempLiteral )) {
                                conflictLiteralList.add( tempLiteral );
                                conflictIntegerLiteralList.add( lit );
                                if (assignedLiterals.indexOf( compTempLiteral ) < backtrackLiteral ) {
                                    if (!assignedLiterals.get(assignedLiterals.indexOf( compTempLiteral )).isForced() ) {
                                        if (!assignedLiterals.get(assignedLiterals.indexOf( compTempLiteral )).isRightBranch() ) {
                                            backtrackLiteral = assignedLiterals.indexOf( compTempLiteral );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

        }

        if ( backtrackLiteral > assignedLiterals.size() ) {
            return -2;
        } else {
            backtrackLiteral = assignedLiterals.get( backtrackLiteral ).getLiteral();
        }

        // Convert the Integer List to an array, the format the Clause object takes.
        conflictClause = new Clause( IntegerListToIntArray( conflictIntegerLiteralList ));
        conflictClause.setConflictClause();

        if ( conflictClause.getSize() < 3 ) {
            return -2;
        }
        if ( conflictClause.getSize() > 9 ) {
            return -2;
        }

        if ( !dpllClauseList.contains( conflictClause ) ) {
            if ( DEBUG ) {
                System.out.println(conflictClause);
                System.out.println("Backtrack to: " + backtrackLiteral);
            }
            dpllClauseList.add( conflictClause );
            return backtrackLiteral;
        }
        else {
            return -2;
        }
    }

    // This method must be called before each iteration through the DPLL function, since the algorithm uses the
    // same clause list for all iterations.
    private void resetClauseListState ( ArrayList<Clause> dpllClauseList ) {
        for (Clause clause : dpllClauseList) {
            clause.resetClause();
        }
    }

    // Takes an ArrayList of Literals that have been assigned and makes them official with the clauseList.
    private void assignLiteralListToClauseList(ArrayList<Clause> dpllClauseList, ArrayList<Literal> currentLiterals) {
        for (Literal literal : currentLiterals) {
            for (Clause clause : dpllClauseList) {
                clause.assign(literal);
            }
        }
    }

    // This function simply converts an Integer List to an int[]
    private int[] IntegerListToIntArray(ArrayList<Integer> list)  {
        int[] ret = new int[list.size()];
        int i = 0;
        for (Integer e : list)
            ret[i++] = e;
        return ret;
    }

    // This method has two functions.  It first looks for clauses that contain all the same literals and adds them
    // to a sub-list of clauses to run DPLL on.  If the result is unsat, the whole formula is unsat.
    // The second function is to reduce the clause list.  Clauses in the form (x + y + z)(x + y + z') will be
    // expanded to (x + y)
    private int expandClauseList() {
        ArrayList<Clause> newClauses = new ArrayList<>(0);
        ArrayList<Clause> clausesToRemove = new ArrayList<>(0);

        // These two loops compare every clause to every other clause.
        for ( Clause clause1 : clauseList ) {
            ArrayList<Clause> dpllClauseSublist = new ArrayList<>();
            for ( Clause clause2 : clauseList ) {
                // checkContradiction looks for two clauses that are different by a single variable.  It returns
                // a contradiction clause that contains only the variables in common.
                int[] newClause = checkContradiction( clause1, clause2 );

                if ( newClause != null) {
                    if ( newClause[0] != 0 ) {
                        // Add to a list of clauses we need to remove.
                        if (!clausesToRemove.contains(clause1)) {
                            clausesToRemove.add( clause1 );
                        }
                        if (!clausesToRemove.contains(clause2)) {
                            clausesToRemove.add( clause2 );
                        }
                        Clause clauseToAdd = new Clause( newClause );
                        // Add to a list of clauses to add.
                        if (!newClauses.contains(clauseToAdd)) {
                            newClauses.add(new Clause( newClause ));
                        }
                    }

                    if (clauseMatchedLiterals(clause1, clause2) == clause1.getSize()) {
                        dpllClauseSublist.add( clause2 );
                    }

                }
            }
            if ( dpllClauseSublist.size() > 2 ) {
                ArrayList<Literal> assignedLiterals = new ArrayList<>(1);
                ArrayList<Literal> dpllLiteralList = clause1.getLiterals();

                DPLL( dpllClauseSublist, assignedLiterals, dpllLiteralList );
                if (!isFormulaSAT) {
                    return -1;
                } else {
                    isFormulaSAT = false;
                }
            }
        }

        Iterator<Clause> iterator;

        // Remove clauses from clauseList
        for (Clause clauseToRemove : clausesToRemove ) {
            iterator = clauseList.iterator();
            while ( iterator.hasNext() ) {
                if (iterator.next() == clauseToRemove) {
                    iterator.remove();
                }
            }
        }

        // Add new clauses to clauseList
        for (Clause clauseToAdd : newClauses ) {
            clauseList.add( new Clause( clauseToAdd ));
        }

        numClauses = clauseList.size();

        return 0;
    }

    // Checks for two clauses to be equivalent, but with one complemented variable.
    private int[] checkContradiction( Clause clause1, Clause clause2 ) {
        ArrayList<Integer> literalMatchCounts;

        literalMatchCounts = clauseMatchedLiteralCount( clause1, clause2 );

        if ( literalMatchCounts != null ) {
            int listSize = clause1.getSize();
            int literalExactMatches = literalMatchCounts.get(1);
            int literalComplementMatches = literalMatchCounts.get(2);
            int complementLiteral = literalMatchCounts.get(3);
            ArrayList<Integer> literalList1 = clause1.getVariables();

            if (literalComplementMatches == 1 && literalExactMatches == (listSize - 1)) {
                ArrayList<Integer> newClause = new ArrayList<>(0);
                for (Integer i : literalList1) {
                    if (Math.abs(i) != Math.abs(complementLiteral)) {
                        newClause.add(i);
                    }
                }

                return IntegerListToIntArray(newClause);
            }
        }
        else return null;

        int[] nothingSpecial = new int[]{0};
        return nothingSpecial;
    }

    // Counts the number of literals two clauses have in common, regardless of their sign.
    private ArrayList<Integer> clauseMatchedLiteralCount( Clause clause1, Clause clause2 ) {
        if (clause1.getSize() != clause2.getSize()) {
            return null;
        }

        ArrayList<Integer> returnCounts = new ArrayList<>(4);

        int listSize = clause1.getSize();

        int matchTracker = 0;
        int perfectMatchTracker = 0;
        int complementTracker = 0;
        int complementLiteral = 0;

        ArrayList<Integer> literalList1 = clause1.getVariables();
        ArrayList<Integer> literalList2 = clause2.getVariables();

        int x;
        int y;
        for ( int i = 0; i < listSize; i++ ) {
            x = literalList1.get(i);
            y = literalList2.get(i);
            if ( Math.abs( x) == Math.abs( y )) {
                matchTracker++;
            }
            if ( x == y ) {
                perfectMatchTracker++;
            }
            if ( x == -1*y ) {
                complementTracker++;
                complementLiteral = x;
            }
        }

        returnCounts.add( matchTracker );
        returnCounts.add( perfectMatchTracker );
        returnCounts.add( complementTracker );
        returnCounts.add( complementLiteral );

        return returnCounts;
    }

    // Counts the number of literals two clauses have in common, regardless of their sign.
    private int clauseMatchedLiterals( Clause clause1, Clause clause2 ) {
        if (clause1.getSize() != clause2.getSize()) {
            return -1;
        }

        int listSize = clause1.getSize();

        int matchTracker = 0;

        ArrayList<Integer> literalList1 = clause1.getVariables();
        ArrayList<Integer> literalList2 = clause2.getVariables();

        int x;
        int y;
        for ( int i = 0; i < listSize; i++ ) {
            x = Math.abs( literalList1.get(i) );
            y = Math.abs( literalList2.get(i) );
            if ( x == y ) {
                matchTracker++;
            }
        }

        return matchTracker;
    }

    // This is a dumb function to pick a new literal to branch on.
    // assignedLiterals is an ArrayList of literals that have already been picked.
    // pickLiteral simply picks a value that has not been picked.
    // If all literals have been picked, it returns -1.
    private int pickLiteral(ArrayList<Literal> assignedLiterals, ArrayList<Literal> allLiterals) {
        Literal oppositeLiteral;
        for ( Literal literal : allLiterals ) {
            oppositeLiteral = new Literal( literal );
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
        int finalValue;

        output.append("RESULT: SAT \n");
        output.append("ASSIGNMENT: ");

        for (Literal literal : formulaSolution) {
            finalLiteral = literal.getLiteral();
            finalValue = 0;
            // if the value assigned to a literal is true, assign value of 1.
            if (literal.getValue()) {
                finalValue = 1;
            }
            output.append(finalLiteral);
            output.append("=");
            output.append(finalValue);
            output.append(" ");
        }

        System.out.println(output.toString());
        System.out.println("Decisions: " + numberOfDecisions);
        System.out.println("Conflicts: " + numberOfConflicts);
    }

    private void recordFormulaSolution( ArrayList<Literal> assignedLiterals ) {
        for ( Literal lit : assignedLiterals ) {
            if ( lit.getValue() ) {
                lit.complement();
                int index = literalList.indexOf( lit );
                literalList.get( index ).complement();
            }
        }
        formulaSolution = literalList;
    }

    private void copyDataStructures(ArrayList<Literal> assignedLiterals, ArrayList<Literal> leftLiteralBranch, ArrayList<Literal> rightLiteralBranch) {
        // Copy the assigned literals to two new lists that will be used in the recursive calls
        for (Literal literal : assignedLiterals) {
            leftLiteralBranch.add(new Literal(literal));
            rightLiteralBranch.add(new Literal(literal));
        }
    }

    private boolean isFormulaSAT() {
        for (int i = 0; i < clauseList.size(); i++) {
            if (!clauseList.get(i).isSAT()) {
                return false;
            }
        }
        return true;
    }

    public void bruteForceSolution() {
        int x = bruteForceSATSolver( clauseList, literalList );

        if ( x == 0 ) {
            printBruteForceSolution();
        } else if ( x == -1 ) {
            System.out.println("No solution!");
        }
    }

    private int bruteForceSATSolver(ArrayList<Clause> bruteClauseList, ArrayList<Literal> bruteLiteralList ) {
        int i, j;
        BigInteger totalPossibilities;

        totalPossibilities = new BigInteger("2");
        totalPossibilities = totalPossibilities.pow(bruteLiteralList.size());

        System.out.println("Total combinations: " + totalPossibilities.toString());

        while (!isFormulaSAT()) {
            incrementLiteralListValues();
            for (i = 0; i < bruteClauseList.size(); i++) {
                for (j = 0; j < bruteLiteralList.size(); j++) {
                    if (!bruteClauseList.get(i).isSAT()) {
                        bruteClauseList.get(i).assignBrute(bruteLiteralList.get(j));
                    }
                }
            }
            totalPossibilities = totalPossibilities.subtract(BigInteger.ONE);
            if (totalPossibilities.equals(BigInteger.ZERO)) break;
        }
        if (isFormulaSAT()) {
            return 0;
        }
        else {
            return -1;
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
        int finalValue;

        output.append("RESULT: SAT \n");
        output.append("ASSIGNMENT: ");

        for (Literal literal : literalList) {
            finalLiteral = literal.getLiteral();
            finalValue = 0;
            // if the value assigned to a literal is true, assign value of 1.
            if (literal.getValue()) {
                finalValue = 1;
            }
            output.append(finalLiteral);
            output.append("=");
            output.append(finalValue);
            output.append(" ");
        }

        System.out.println(output.toString());

    }

    void setDEBUG () {
        DEBUG = true;
    }

}
