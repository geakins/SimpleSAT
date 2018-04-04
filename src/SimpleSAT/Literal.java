package SimpleSAT;

public class Literal {
    // literal is the actual # in the CNF file of the literal.  Value is always positive.
    private int literal;
    // value is the T or F value assigned to the literal during the algorithm.
    private boolean value;
    // assigned is a flag that marks if the literal has been assigned or not.
    private boolean assigned;
    // Counts the number of appearances in the formula.
    private int appearances;

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
        appearances = literalObject.appearances;
    }

    void assign(boolean val) {
        value = val;
        assigned = true;
    }

    void setLiteralCount(int count) {
        appearances = count;
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

    int getAppearances() {
        return appearances;
    }

    // Set the number of the literal
    void set(int lit) {
        this.literal = lit;
    }

    @Override
    public String toString() {
        String output;
        output = literal + " " + Boolean.toString(value);
        return output;
    }

    @Override
    public boolean equals(Object object)
    {
        if (object instanceof Literal)
        {
            return ((this.literal == ((Literal) object).literal) && (this.value == ((Literal) object).value));
        }
        return false;
    }

}
