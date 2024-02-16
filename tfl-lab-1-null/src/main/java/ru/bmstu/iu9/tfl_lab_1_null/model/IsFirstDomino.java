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
public class IsFirstDomino implements ToTerm {
    private DominoIndex dominoIndex;

    @Override
    public String toString() {
        return String.format("!IsFirstDomino_%s", dominoIndex.getIndex());
    }

    public Term toTerm() {
        return new ValueTerm(toString());
    }

    public static IsFirstDomino getByDominoIndex(List<IsFirstDomino> isFirstDominoes, DominoIndex dominoIndex) {
        for (IsFirstDomino isFirstDomino : isFirstDominoes) {
            if (isFirstDomino.getDominoIndex().equals(dominoIndex)) {
                return isFirstDomino;
            }
        }
        return null;
    }
}
