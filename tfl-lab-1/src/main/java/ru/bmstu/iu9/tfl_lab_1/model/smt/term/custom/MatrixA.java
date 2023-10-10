package ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.Term;

@Getter
@AllArgsConstructor
public class MatrixA implements Term {
    private final String name = "and";
    private Term term00;
    private Term term01;
    private Term term10;
    private Term term11;

    @Override
    public String toString() {
        return "("+name+" " + term00 + " " + term01 + " " + term10 + " " + term11 + ")";
    }
}
