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
public class CountLetter implements ToTerm {
    private Type type;
    private DominoIndex dominoIndex;
    private Character letter;

    @Override
    public String toString() {
        return String.format("CountLetter_%s_%s_%s", type, dominoIndex.getIndex(), letter);
    }

    public Term toTerm() {
        return new ValueTerm(toString());
    }

    public static CountLetter getByDominoIndex(List<CountLetter> countLetters, DominoIndex dominoIndex) {
        for (CountLetter countLetter : countLetters) {
            if (countLetter.getDominoIndex().equals(dominoIndex)) {
                return countLetter;
            }
        }
        return null;
    }

    public enum Type {
        UP,
        DOWN;

        @Override
        public String toString() {
            return switch (this) {
                case UP -> "up";
                case DOWN -> "down";
            };
        }
    }
}
