package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import java.util.ArrayList;
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

    public GrammarUnit get(int index) {
        return grammarUnits.get(index);
    }

    public GrammarString substring(int startIndex, int endIndex) {
        List<GrammarUnit> newSymbols = new ArrayList<>();
        for (int i = startIndex; i < endIndex; i++) {
            newSymbols.add(this.grammarUnits.get(i));
        }
        return new GrammarString(newSymbols);
    }

    public GrammarString substring(int index) {
        List<GrammarUnit> newSymbols = new ArrayList<>();
        for (int i = index; i < this.grammarUnits.size(); i++) {
            newSymbols.add(this.grammarUnits.get(i));
        }
        return new GrammarString(newSymbols);
    }

    @Override
    public String toString() {
        return Arrays.toString(grammarUnits.toArray());
    }
}
