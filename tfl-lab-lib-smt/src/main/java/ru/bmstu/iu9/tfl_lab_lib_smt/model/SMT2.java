package ru.bmstu.iu9.tfl_lab_lib_smt.model;

import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.part.*;

import java.util.ArrayList;
import java.util.List;

@Getter
public class SMT2 {
    private final String header = """
            (set-logic QF_NIA)
            """;

    private final List<DeclareConstant> declareConstants = new ArrayList<>();

    private final List<DefineConstant> defineConstants = new ArrayList<>();

    private final List<Assert> asserts = new ArrayList<>();

    private final String footer = """
            (check-sat)
            (get-model)
            """;

    public SMT2(List<DeclareConstant> declareConstants, List<DefineConstant> defineConstants, List<Assert> asserts) {
        this.declareConstants.addAll(declareConstants);
        this.defineConstants.addAll(defineConstants);
        this.asserts.addAll(asserts);
    }

    @Override
    public String toString() {
        StringBuilder defineConstants = new StringBuilder();
        for (DefineConstant defineConstant : this.defineConstants) {
            defineConstants.append(defineConstant).append("\n");
        }
        StringBuilder declareConstants = new StringBuilder();
        for (DeclareConstant declareConstant : this.declareConstants) {
            declareConstants.append(declareConstant).append("\n");
        }
        StringBuilder asserts = new StringBuilder();
        for (Assert assertA : this.asserts) {
            asserts.append(assertA).append("\n");
        }
        return header + "\n" +
                defineConstants + "\n" +
                declareConstants + "\n" +
                asserts + "\n" +
                footer;
    }
}
