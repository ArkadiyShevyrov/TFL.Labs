package ru.bmstu.iu9.tfl_lab_1.service.logic;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_1.model.rest.SrsString;
import ru.bmstu.iu9.tfl_lab_1.model.smt.part.Assert;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.basic.*;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom.MatrixA;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom.MatrixB;
import java.util.ArrayList;
import java.util.List;

@UtilityClass
public class AssertLogic {
    public List<Assert> getAssertVariables(List<String> alphabetLetters) {
        List<Assert> variables = new ArrayList<>();
        for (String charA : alphabetLetters) {
            List<Assert> listA = getAssertA(charA);
            List<Assert> listB = getAssertB(charA);
            variables.addAll(listA);
            variables.addAll(listB);
        }
        return variables;
    }

    public List<Assert> getAssertsMatrix(List<SrsString> srsStrings) {
        List<Assert> asserts = new ArrayList<>();
        for (SrsString srsString : srsStrings) {
            asserts.addAll(getAsserts(srsString.getSrsString()));
        }
        return asserts;
    }

    private List<Assert> getAsserts(String trsSting) {
        List<String> split = List.of(trsSting.split("->"));
        String left = split.get(0);
        String right = split.get(1);
        ArrayList<Assert> asserts = new ArrayList<>();
        asserts.add(getAssertX(left, right));
        asserts.add(getAssertC(left, right));
        return asserts;
    }

    private static Assert getAssertX(String left, String right) {
        MatrixA leftMatrixA = MatrixLogic.generateMatrixByX(left);
        MatrixA rightMatrixA = MatrixLogic.generateMatrixByX(right);
        return new Assert(MatrixLogic.moreMatrixAA(leftMatrixA, rightMatrixA));
    }

    private static Assert getAssertC(String left, String right) {
        MatrixB leftMatrixB = MatrixLogic.generateMatrixByC(left);
        MatrixB rightMatrixB = MatrixLogic.generateMatrixByC(right);
        return new Assert(MatrixLogic.moreMatrixBB(leftMatrixB, rightMatrixB));
    }

    private List<Assert> getAssertB(String charA) {
        List<Assert> asserts = new ArrayList<>();
        asserts.add(new Assert(new OrTerm(
                new GreaterTerm(
                        new ValueTerm("b" + charA + "0"),
                        new ValueTerm("-1")),
                new AndTerm(
                        new EqualTerm(
                                new ValueTerm("0"),
                                new ValueTerm("b" + charA + "0")
                        ),
                        new EqualTerm(
                                new ValueTerm("0"),
                                new ValueTerm("b" + charA + "1")
                        )
                ))));
        asserts.add(new Assert(new GreaterEqualTerm(
                new ValueTerm("b" + charA + "1"),
                new ValueTerm("-1"))));
        return asserts;
    }

    private List<Assert> getAssertA(String charA) {
        List<Assert> asserts = new ArrayList<>();
        asserts.add(new Assert(new GreaterTerm(
                new ValueTerm("a" + charA + "00"),
                new ValueTerm("-1"))));
        asserts.add(new Assert(new GreaterEqualTerm(
                new ValueTerm("a" + charA + "01"),
                new ValueTerm("-1"))));
        asserts.add(new Assert(new GreaterEqualTerm(
                new ValueTerm("a" + charA + "10"),
                new ValueTerm("-1"))));
        asserts.add(new Assert(new GreaterEqualTerm(
                new ValueTerm("a" + charA + "11"),
                new ValueTerm("-1"))));
        return asserts;
    }
}
