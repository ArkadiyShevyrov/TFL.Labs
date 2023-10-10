package ru.bmstu.iu9.tfl_lab_1.model.smt.term.basic;

import lombok.AllArgsConstructor;
import lombok.Setter;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.Term;

@Setter
@AllArgsConstructor
public class LessTerm implements Term {
    private final String name = "<";
    private Term one;
    private Term two;

    @Override
    public String toString() {
        return String.format("(%s %s %s)", name, one, two);
    }
}
