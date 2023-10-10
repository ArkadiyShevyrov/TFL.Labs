package ru.bmstu.iu9.tfl_lab_1.model.smt.part;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.Term;

@Getter
@AllArgsConstructor
public class DefineFun {
    private final String name = "define-fun";
    private String nameFun;
    private String vars;
    private String outputType;
    private Term term;

    @Override
    public String toString() {
        return String.format("(%s %s %s %s\n%s)", name, nameFun, vars, outputType, term);
    }

    ///(define-fun " + name + " ((a Int) (b Int)) Int\n" +
}
