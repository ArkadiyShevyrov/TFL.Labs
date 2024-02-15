package ru.bmstu.iu9.tfl_lab_1_null.model.smt.term.basic;

import lombok.AllArgsConstructor;
import lombok.Setter;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.interfaces.Term;

@Setter
@AllArgsConstructor
public class GreaterEqualTerm implements Term {
    private final String name = ">=";
    private Term one;
    private Term two;

    @Override
    public String toString() {
        return String.format("(%s %s %s)", name, one, two);
    }
}
