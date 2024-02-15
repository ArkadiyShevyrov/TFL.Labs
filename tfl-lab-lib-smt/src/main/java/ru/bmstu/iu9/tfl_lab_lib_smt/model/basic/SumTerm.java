package ru.bmstu.iu9.tfl_lab_lib_smt.model.basic;

import lombok.AllArgsConstructor;
import lombok.Setter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;

import java.util.List;

@Setter
@AllArgsConstructor
public class SumTerm implements Term {
    private final String name = "+";
    private List<Term> terms;

    public SumTerm(Term... terms) {
        this.terms = List.of(terms);
    }

    public SumTerm(Term one, Term two) {
        this.terms.add(one);
        this.terms.add(two);
    }

    @Override
    public String toString() {
        return String.format("(%s %s)", name,
                this.terms.stream()
                        .map(Object::toString)
                        .reduce((s1, s2) -> s1 + " " + s2).orElse(""));
    }
}
