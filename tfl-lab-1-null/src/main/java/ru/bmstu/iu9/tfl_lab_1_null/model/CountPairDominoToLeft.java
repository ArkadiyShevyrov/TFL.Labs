package ru.bmstu.iu9.tfl_lab_1_null.model;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.ToTerm;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.basic.ValueTerm;

import java.util.ArrayList;
import java.util.List;

@Getter
@EqualsAndHashCode
@AllArgsConstructor
public class CountPairDominoToLeft implements ToTerm {
    private DominoIndex left;
    private DominoIndex right;

    @Override
    public String toString() {
        return String.format("!CountPairDominoToLeft_%s_%s", left.getIndex(), right.getIndex());
    }

    @Override
    public Term toTerm() {
        return new ValueTerm(toString());
    }

    public static List<CountPairDominoToLeft> getAllByDominoIndexLeft
            (List<CountPairDominoToLeft> list, DominoIndex left) {
        List<CountPairDominoToLeft> resultList = new ArrayList<>();
        for (CountPairDominoToLeft countPairDominoToLeft : list) {
            if (countPairDominoToLeft.getLeft().equals(left)) {
                resultList.add(countPairDominoToLeft);
            }
        }
        return resultList;
    }

    public static List<CountPairDominoToLeft> getAllByDominoIndexRight
            (List<CountPairDominoToLeft> list, DominoIndex right) {
        List<CountPairDominoToLeft> resultList = new ArrayList<>();
        for (CountPairDominoToLeft countPairDominoToLeft : list) {
            if (countPairDominoToLeft.getRight().equals(right)) {
                resultList.add(countPairDominoToLeft);
            }
        }
        return resultList;
    }

    public static CountPairDominoToLeft getAllByDominoTwoIndex
            (List<CountPairDominoToLeft> list, DominoIndex left, DominoIndex right) {
        for (CountPairDominoToLeft countPairDominoToLeft : list) {
            if (countPairDominoToLeft.getLeft().equals(left) &&
                    countPairDominoToLeft.getRight().equals(right)) {
                return countPairDominoToLeft;
            }
        }
        return null;
    }
}
