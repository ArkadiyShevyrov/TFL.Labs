package ru.bmstu.iu9.tfl_lab_lib_smt.model.basic;

import lombok.AllArgsConstructor;
import lombok.Setter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;


@Setter
@AllArgsConstructor
public class MinusTerm implements Term {
    private final String name = "-";
    private Term one;
    private Term two;

    @Override
    public String toString() {
        return String.format("(%s %s %s)", name, one, two);
    }
}
