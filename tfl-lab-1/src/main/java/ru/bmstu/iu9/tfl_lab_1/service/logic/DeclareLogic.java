package ru.bmstu.iu9.tfl_lab_1.service.logic;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_1.model.smt.part.DeclareFun;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.basic.ValueTerm;
import java.util.ArrayList;
import java.util.List;

@UtilityClass
public class DeclareLogic {
    public List<DeclareFun> getDeclares(List<String> alphabetLetters) {
        List<DeclareFun> declareFuns = new ArrayList<>();
        for (String charA : alphabetLetters) {
            List<DeclareFun> listA = getListDeclareA(charA);
            List<DeclareFun> listB = getListDeclareB(charA);
            declareFuns.addAll(listA);
            declareFuns.addAll(listB);
        }
        return declareFuns;
    }

    private List<DeclareFun> getListDeclareB(String charA) {
        List<DeclareFun> declareFuns = new ArrayList<>();
        declareFuns.add(new DeclareFun(new ValueTerm("b" + charA + "0")));
        declareFuns.add(new DeclareFun(new ValueTerm("b" + charA + "1")));
        return declareFuns;
    }

    private List<DeclareFun> getListDeclareA(String charA) {
        List<DeclareFun> declareFuns = new ArrayList<>();
        declareFuns.add(new DeclareFun(new ValueTerm("a" + charA + "00")));
        declareFuns.add(new DeclareFun(new ValueTerm("a" + charA + "01")));
        declareFuns.add(new DeclareFun(new ValueTerm("a" + charA + "10")));
        declareFuns.add(new DeclareFun(new ValueTerm("a" + charA + "11")));
        return declareFuns;
    }
}
