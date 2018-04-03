package SimpleSAT;

// Stores each clause of the function in the same format as given in the CNF file.
// That is, the variables[] array is an integer list of numbered literals
// Each literal is numbered.  A '-' in front of a literal represents a complimented variable.

import java.util.Arrays;

public class Clause {
    private int variables[];
    private int size;
    // Values is a list of values assigned to each literal of variables[].
    private boolean values[];
    // Assigned marks if each literal has a values assigned to it.
    private boolean assigned[];
    // Assigned to true if the clause is satisfied.
    private boolean isSAT;

    // The constructor method.  This takes the array of integers in a[] and assigns them to the variables array.  The length and
    Clause(final int a[]) {
        this.variables = a;
        this.size = a.length;
        this.values = new boolean[a.length];
        this.assigned = new boolean[a.length];
        Arrays.fill(this.values, false);
        Arrays.fill(this.assigned, false);
    }

    Clause (Clause clause) {
        variables = clause.variables;
        size = clause.size;
        values = clause.values;
        assigned = clause.assigned;
        isSAT = clause.isSAT;
    }

    int size() {
        return size;
    }

    int get(final int index) {
        return variables[index];
    }

    boolean isSAT() {
        return isSAT;
    }

    void assign(Literal literalToAssign) {
        for (int i = 0; i < size; i++) {
            if (Math.abs(variables[i]) == literalToAssign.getLiteral()) {
                assigned[i] = true;
                values[i] = literalToAssign.getValue();
                if (variables[i] > 0 && values[i]) {
                    isSAT = true;
                }
                else if (variables[i] < 0 && !values[i]) {
                    isSAT = true;
                }
            }
        }
    }

    void assignBrute(Literal literalToAssign) {
        for (int i = 0; i < size; i++) {
            if (Math.abs(variables[i]) == literalToAssign.getLiteral()) {
                values[i] = literalToAssign.getValue();
                evaluateSAT();
            }
        }
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

    @Override
    public String toString() {
        final String delimiter = " ";
        StringBuilder output = new StringBuilder();

        for (int v : variables) {
            output.append(v);
            output.append(delimiter);
        }

        return output.toString();
    }
}