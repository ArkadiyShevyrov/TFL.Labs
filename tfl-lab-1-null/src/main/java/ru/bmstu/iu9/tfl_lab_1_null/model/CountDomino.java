package ru.bmstu.iu9.tfl_lab_1_null.model;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.ToTerm;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.basic.ValueTerm;

import java.util.List;

@Getter
@EqualsAndHashCode
@AllArgsConstructor
public class CountDomino implements ToTerm {
    private DominoIndex dominoIndex;

    @Override
    public String toString() {
        return String.format("!CountDomino_%s", dominoIndex.getIndex());
    }

    public Term toTerm() {
        return new ValueTerm(toString());
    }

    public static CountDomino getByDominoIndex(List<CountDomino> countDominoes, DominoIndex dominoIndex) {
        for (CountDomino countDomino : countDominoes) {
            if (countDomino.getDominoIndex().equals(dominoIndex)) {
                return countDomino;
            }
        }
        return null;
    }
}
