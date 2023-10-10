package ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.Term;

@Getter
@AllArgsConstructor
public class MatrixB implements Term {
    private final String name = "and";
    private Term term0;
    private Term term1;

    @Override
    public String toString() {
        return "(" + name + " " + term0 + " " + term1 + ")";
    }
}
