package ru.bmstu.iu9.tfl_lab_1.model.smt;

import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_1.model.smt.part.Assert;
import ru.bmstu.iu9.tfl_lab_1.model.smt.part.DeclareFun;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.CustomTerm;
import java.util.List;

@Getter
public class SMT2 {
    private final String header = """
            (set-logic QF_NIA)
            """;

    private final List<CustomTerm> customTerms;

    private final List<DeclareFun> declareFuns;

    private final List<Assert> asserts;

    private final String footer = """
            (check-sat)
            (get-model)
            (exit)
            """;

    public SMT2(List<CustomTerm> customTerms, List<DeclareFun> declareFuns, List<Assert> asserts) {
        this.customTerms = customTerms;
        this.declareFuns = declareFuns;
        this.asserts = asserts;
    }

    @Override
    public String toString() {
        StringBuilder customTerms = new StringBuilder();
        for (CustomTerm customTerm : this.customTerms) {
            customTerms.append(customTerm.getDefineFun()).append("\n");
        }
        StringBuilder declareFuns = new StringBuilder();
        for (DeclareFun declareFun : this.declareFuns) {
            declareFuns.append(declareFun).append("\n");
        }
        StringBuilder asserts = new StringBuilder();
        for (Assert assertA : this.asserts) {
            asserts.append(assertA).append("\n");
        }
        return header + "\n" +
                customTerms + "\n" +
                declareFuns + "\n" +
                asserts + "\n" +
                footer;
    }
}
