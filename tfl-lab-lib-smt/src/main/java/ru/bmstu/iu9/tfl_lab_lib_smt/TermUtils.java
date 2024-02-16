package ru.bmstu.iu9.tfl_lab_lib_smt;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.ToTerm;

import java.util.ArrayList;
import java.util.List;

@UtilityClass
public class TermUtils {
    public List<Term> toListTerm(List<? extends ToTerm> toTerms) {
        List<Term> terms = new ArrayList<>();
        for (ToTerm toTerm : toTerms) {
            terms.add(toTerm.toTerm());
        }
        return terms;
    }
}
