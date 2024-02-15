package ru.bmstu.iu9.tfl_lab_1_null.model.smt.term.basic;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.Setter;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.interfaces.Term;

@Getter
@Setter
@AllArgsConstructor
public class ValueTerm implements Term {
    private String value;

    @Override
    public String toString() {
        return value;
    }
}
