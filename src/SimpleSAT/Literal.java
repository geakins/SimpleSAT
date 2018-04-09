package SimpleSAT;

public class Literal {
    // literal is the actual # in the CNF file of the literal.  Value is always positive.
    private int literal;
    // value is the T or F value assigned to the literal during the algorithm.
    private boolean value;
    // Counts the number of appearances in the formula.
    private int appearances;
    // If the literal is forced, it is marked as such.
    private boolean forced;

    // The constructor method.  This takes the array of integers in a[] and assigns them to the variables array.
    Literal(final int a) {
        this.literal = a;
        this.value = false;
        this.appearances = 0;
        this.forced = false;
    }

    Literal(final int a, boolean v) {
        this.literal = a;
        this.value = v;
    }

    Literal (Literal literalObject) {
        literal = literalObject.literal;
        value = literalObject.value;
        appearances = literalObject.appearances;
        forced = literalObject.forced;
    }

    void assign(boolean val) {
        value = val;
    }

    void setLiteralCount(int count) {
        appearances = count;
    }

    void setLiteral(int lit) {
        literal = lit;
    }

    void setValue( boolean val ) {
        value = val;
    }

    void setForced () {
        forced = true;
    }

    boolean getForced () {
        return forced;
    }

    void complement () {
        value = !value;
    }

    int getLiteral() {
        return literal;
    }

    int getFullLiteral() {
        if ( value ) return literal;
        else return -1*literal;
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
