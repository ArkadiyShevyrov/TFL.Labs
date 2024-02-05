package ru.bmstu.iu9.tfl_lab_1_null.model.smt;

import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.part.Assert;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.part.DeclareConst;

import java.util.List;

@Getter
public class SMT2 {
    private final String header = """
            (set-logic QF_NIA)
            """;

    private final List<DeclareConst> declareConstants;

    private final List<Assert> asserts;

    private final String footer = """
            (check-sat)
            (get-model)
            (exit)
            """;

    public SMT2(List<DeclareConst> declareConstants, List<Assert> asserts) {
        this.declareConstants = declareConstants;
        this.asserts = asserts;
    }

    @Override
    public String toString() {
        StringBuilder declareConstants = new StringBuilder();
        for (DeclareConst declareConst : this.declareConstants) {
            declareConstants.append(declareConst).append("\n");
        }
        StringBuilder asserts = new StringBuilder();
        for (Assert assertA : this.asserts) {
            asserts.append(assertA).append("\n");
        }
        return header + "\n" +
                declareConstants + "\n" +
                asserts + "\n" +
                footer;
    }
}
