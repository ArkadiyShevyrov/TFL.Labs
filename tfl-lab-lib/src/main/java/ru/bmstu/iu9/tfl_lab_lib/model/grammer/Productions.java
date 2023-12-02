package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.*;

@Getter
@AllArgsConstructor
public class Productions {
    private HashMap<Variable, List<GrammarString>> tableProductions;

    public Productions() {
        tableProductions = new HashMap<>();
    }

    public void putToTable(Variable variable, GrammarString grammarString) {
        tableProductions
                .computeIfAbsent(variable, k -> new ArrayList<>())
                .add(grammarString);
    }

    public void putToTable(Variable variable, GrammarString... grammarStrings) {
        for (GrammarString grammarString : grammarStrings) {
            putToTable(variable, grammarString);
        }
    }
}
