package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import java.util.Arrays;
import java.util.List;

@Getter
@AllArgsConstructor
@EqualsAndHashCode
public class GrammarString {
    private List<GrammarUnit> grammarUnits;

    public GrammarString(GrammarUnit... grammarUnits) {
        this.grammarUnits = Arrays.stream(grammarUnits).toList();
    }

    public int size() {
        return grammarUnits.size();
    }

    @Override
    public String toString() {
        return Arrays.toString(grammarUnits.toArray());
    }
}
