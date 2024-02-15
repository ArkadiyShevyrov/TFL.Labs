package ru.bmstu.iu9.tfl_lab_1_null.model.smt.part;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.interfaces.Term;

@Getter
@AllArgsConstructor
public class Assert {
    private Term term;

    @Override
    public String toString() {
        return "(assert " + term + ")";
    }
}
