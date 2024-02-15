package ru.bmstu.iu9.tfl_lab_1_null.model.smt.term.basic;

import lombok.AllArgsConstructor;
import lombok.Setter;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.interfaces.Term;

import java.util.List;

@Setter
@AllArgsConstructor
public class SumTerm implements Term {
    private final String name = "+";
    private List<Term> terms;

    public SumTerm(Term... terms) {
        this.terms = List.of(terms);
    }

    @Override
    public String toString() {
        return String.format("(%s %s)", name,
                this.terms.stream()
                        .map(Object::toString)
                        .reduce((s1, s2) -> s1 + " " + s2).orElse(""));
    }
}
