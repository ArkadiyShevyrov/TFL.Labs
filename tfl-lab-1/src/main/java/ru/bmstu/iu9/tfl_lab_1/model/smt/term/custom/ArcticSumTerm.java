package ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;
import ru.bmstu.iu9.tfl_lab_1.model.smt.part.DefineFun;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.basic.*;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.CustomTerm;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.Term;

@Getter
@AllArgsConstructor
@NoArgsConstructor
public class ArcticSumTerm implements CustomTerm {
    private final String name = "arcticSum";
    private Term one;
    private Term two;

    @Override
    public String toString() {
        return String.format("(%s %s %s)", name, one, two);
    }

    @Override
    public String getDefineFun() {
        return new DefineFun(
                name, "((a Int) (b Int))", "Int",
                new IteTerm(
                        new AndTerm(
                                new GreaterTerm(
                                        new ValueTerm("a"),
                                        new ValueTerm("-1")),
                                new GreaterTerm(
                                        new ValueTerm("b"),
                                        new ValueTerm("-1"))),
                        new SumTerm(
                                new ValueTerm("a"),
                                new ValueTerm("b")),
                        new IteTerm(
                                new LessEqualTerm(
                                        new ValueTerm("a"),
                                        new ValueTerm("-1")),
                                new ValueTerm("b"),
                                new ValueTerm("a")))
        ).toString();
    }
}
