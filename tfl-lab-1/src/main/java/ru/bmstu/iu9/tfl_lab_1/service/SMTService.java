package ru.bmstu.iu9.tfl_lab_1.service;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import ru.bmstu.iu9.tfl_lab_1.model.rest.SrsString;
import ru.bmstu.iu9.tfl_lab_1.model.smt.SMT2;
import ru.bmstu.iu9.tfl_lab_1.model.smt.part.Assert;
import ru.bmstu.iu9.tfl_lab_1.model.smt.part.DeclareFun;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom.ArcticMaxTerm;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom.ArcticMoreTerm;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom.ArcticSumTerm;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.interfaces.CustomTerm;
import ru.bmstu.iu9.tfl_lab_1.service.logic.AssertLogic;
import ru.bmstu.iu9.tfl_lab_1.service.logic.DeclareLogic;
import ru.bmstu.iu9.tfl_lab_1.utils.StringUtils;
import java.util.ArrayList;
import java.util.List;

@Slf4j
@Service
public class SMTService {
    public SMT2 generateFileSMT2(List<SrsString> srsStrings) {
        List<String> alphabetLetters = StringUtils.getAlphabetLetters(srsStrings);
        List<CustomTerm> customTerms = new ArrayList<>();
        customTerms.add(new ArcticMaxTerm());
        customTerms.add(new ArcticMoreTerm());
        customTerms.add(new ArcticSumTerm());
        List<DeclareFun> declareFuns = DeclareLogic.getDeclares(alphabetLetters);
        List<Assert> asserts = new ArrayList<>();
        asserts.addAll(AssertLogic.getAssertsMatrix(srsStrings));
        asserts.addAll(AssertLogic.getAssertVariables(alphabetLetters));
        return new SMT2(customTerms, declareFuns, asserts);
    }

    public String smtGen(String string) {
        try (Context context = new Context()) {
            Solver solver = context.mkSimpleSolver();
            solver.fromString(string);
            return solver.check().toString();
        }

    }
}
