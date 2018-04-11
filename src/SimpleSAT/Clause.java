package SimpleSAT;

// Stores each clause of the function in the same format as given in the CNF file.
// That is, the variables[] array is an integer list of numbered literals
// Each literal is numbered.  A '-' in front of a literal represents a complimented variable.


import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;

public class Clause {
    private int variables[];
    private int size;
    // Values is a list of values assigned to each literal of variables[].
    private boolean values[];
    // Assigned marks if each literal has a values assigned to it.
    private boolean assigned[];
    // Assigned to true if the clause is satisfied.
    private boolean isSAT;
    // Counts the number of literals unassigned.  Clause is unit when this reaches 1.
    private int numberUnassigned;

    // The constructor method.  This takes the array of integers in a[] and assigns them to the variables array.  The length and
    Clause(final int a[]) {
        this.variables = a;

        ArrayList<Integer> sorterList = new ArrayList<>(0);

        for (int x : a ) {
            sorterList.add( x );
        }

        Collections.sort(sorterList, new Comparator<Integer>() {
            public int compare(Integer o1, Integer o2) {
                return Integer.compare(Math.abs(o1), Math.abs(o2));
            }
        });

        variables = IntegerListToIntArray( sorterList );

        this.size = a.length;
        this.values = new boolean[a.length];
        this.assigned = new boolean[a.length];
        this.numberUnassigned = a.length;
        Arrays.fill(this.values, false);
        Arrays.fill(this.assigned, false);
    }

    // Constructor for deep copy.
    Clause (Clause clause) {
        size = clause.size;
        variables = new int[clause.variables.length];
        values = new boolean[clause.values.length];
        assigned = new boolean[clause.assigned.length];
        for (int i = 0; i < clause.values.length; i++) {
            variables[i] = clause.variables[i];
            values[i] = clause.values[i];
            assigned[i] = clause.assigned[i];
        }
        numberUnassigned = clause.numberUnassigned;
        isSAT = clause.isSAT;
    }

    boolean isSAT() {
        return isSAT;
    }

    // When run, if the clause is a unit clause, it will return the variable that has not yet been assigned.
    // Otherwise, return 0
    int findImplications() {
        if (isSAT) return 0;
        if (numberUnassigned == 1) {
            for (int i = 0; i < size; i++) {
                if (!assigned[i]) {
                    return variables[i];
                }
            }
        }
        return 0;
    }

    void assign(Literal literalToAssign) {
        for (int i = 0; i < size; i++) {
            if (Math.abs(variables[i]) == literalToAssign.getLiteral()) {
                assigned[i] = true;
                numberUnassigned--;
                values[i] = literalToAssign.getValue();
                if ((variables[i] > 0 && values[i]) || (variables[i] < 0 && !values[i])) {
                    isSAT = true;
                }
            }
        }
    }

    void resetClause() {
        for (int i = 0; i < size; i++) {
            assigned[i] = false;
        }
        isSAT = false;
        numberUnassigned = size;
    }

    void assignBrute(Literal literalToAssign) {
        for (int i = 0; i < size; i++) {
            if (Math.abs(variables[i]) == literalToAssign.getLiteral()) {
                values[i] = literalToAssign.getValue();
                evaluateSAT();
            }
        }
    }

    boolean literalExists(Literal literal) {
        for (int i : variables ) {
            if (Math.abs(literal.getLiteral()) == i) {
                return true;
            }
        }
        return false;
    }

    boolean containsLiteral(int literal) {
        for ( int lit : variables ) {
            if ( Math.abs(lit) == Math.abs(literal) ) {
                return true;
            }
        }
        return false;
    }

    ArrayList<Integer> getVariables() {
        ArrayList<Integer> clauseArray = new ArrayList<>(0);
        for ( int lit : variables ) {
            clauseArray.add( lit );
        }
        return clauseArray;
    }

    ArrayList<Literal> getLiterals() {
        ArrayList<Literal> literalList = new ArrayList<>();
        for (int lit : variables ) {
            Literal newLit = new Literal( lit );
            literalList.add( newLit );
        }
        return literalList;
    }

    int getSize() {
        return size;
    }

    private void evaluateSAT() {
        isSAT = false;
        for (int i = 0; i < size; i++) {
            if (variables[i] > 0 && values[i]) {
                isSAT = true;
                return;
            }
            else if (variables[i] < 0 && !values[i]) {
                isSAT = true;
                return;
            }
        }
    }

    private int[] IntegerListToIntArray(ArrayList<Integer> list)  {
        int[] ret = new int[list.size()];
        int i = 0;
        for (Integer e : list)
            ret[i++] = e;
        return ret;
    }

    @Override
    public String toString() {
        final String delimiter = " ";
        StringBuilder output = new StringBuilder();

        for (int v : variables) {
            output.append(v);
            output.append(delimiter);
        }

        output.append (isSAT);

        return output.toString();
    }

    @Override
    public boolean equals(Object object)
    {
        if (object instanceof Clause)
        {
            if (variables.length != ((Clause) object).variables.length) {
                return false;
            } else {
                for (int i = 0; i < variables.length; i++) {
                    if (variables[i] != ((Clause) object).variables[i]) {
                        return false;
                    }
                }
            }
        }
        else {
            return false;
        }
        return true;
    }
}