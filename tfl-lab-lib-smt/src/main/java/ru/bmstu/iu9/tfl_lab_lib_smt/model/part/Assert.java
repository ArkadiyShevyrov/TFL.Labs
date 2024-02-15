package ru.bmstu.iu9.tfl_lab_lib_smt.model.part;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;


@Getter
@AllArgsConstructor
public class Assert {
    private Term term;

    @Override
    public String toString() {
        return "(assert " + term + ")";
    }
}
