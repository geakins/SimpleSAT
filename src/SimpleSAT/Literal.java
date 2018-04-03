package SimpleSAT;

public class Literal {
    // literal is the actual # in the CNF file of the literal.
    private int literal;
    // value is the T or F value assigned to the literal during the algorithm.
    private boolean value;
    // assigned is a flag that marks if the literal has been assigned or not.
    private boolean assigned;

    // The constructor method.  This takes the array of integers in a[] and assigns them to the variables array.
    Literal(final int a) {
        this.literal = a;
        this.value = false;
        this.assigned = false;
    }

    Literal(final int a, boolean v) {
        this.literal = a;
        this.value = v;
        this.assigned = true;
    }

    Literal (Literal literalObject) {
        literal = literalObject.literal;
        value = literalObject.value;
        assigned = literalObject.assigned;
    }

    void assign(boolean val) {
        value = val;
        assigned = true;
    }

    boolean isAssigned() {
        return assigned;
    }

    int getLiteral() {
        return literal;
    }

    boolean getValue() {
        return value;
    }

    // Set the number of the literal
    void set(int lit) {
        this.literal = lit;
    }

    @Override
    public String toString() {
        String output = "";
        output = output + literal;
        return output;
    }

    @Override
    public boolean equals(Object object)
    {
        if (object instanceof Literal)
        {
            return (this.literal == ((Literal) object).literal);
        }
        return false;
    }

}
