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
public class CountPairDominoToRight implements ToTerm {
    private DominoIndex left;
    private DominoIndex right;

    @Override
    public String toString() {
        return String.format("!CountPairDominoToRight_%s_%s", left.getIndex(), right.getIndex());
    }

    public Term toTerm() {
        return new ValueTerm(toString());
    }

    public static List<CountPairDominoToRight> getAllByDominoIndexLeft
            (List<CountPairDominoToRight> list, DominoIndex left) {
        List<CountPairDominoToRight> resultList = new ArrayList<>();
        for (CountPairDominoToRight countPairDominoToRight : list) {
            if (countPairDominoToRight.getLeft().equals(left)) {
                resultList.add(countPairDominoToRight);
            }
        }
        return resultList;
    }

    public static List<CountPairDominoToRight> getAllByDominoIndexRight
            (List<CountPairDominoToRight> list, DominoIndex right) {
        List<CountPairDominoToRight> resultList = new ArrayList<>();
        for (CountPairDominoToRight countPairDominoToRight : list) {
            if (countPairDominoToRight.getRight().equals(right)) {
                resultList.add(countPairDominoToRight);
            }
        }
        return resultList;
    }

    public static CountPairDominoToRight getAllByDominoTwoIndex
            (List<CountPairDominoToRight> list, DominoIndex left, DominoIndex right) {
        for (CountPairDominoToRight countPairDominoToRight : list) {
            if (countPairDominoToRight.getLeft().equals(left) &&
                    countPairDominoToRight.getRight().equals(right)) {
                return countPairDominoToRight;
            }
        }
        return null;
    }
}
