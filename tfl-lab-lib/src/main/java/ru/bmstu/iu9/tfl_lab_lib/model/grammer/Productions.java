package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import java.util.*;

@Getter
@AllArgsConstructor
public class Productions {
    private HashMap<Variable, List<GrammarString>> tableProductions;

    public Productions() {
        tableProductions = new HashMap<>();
    }

    public Productions(Productions productions) {
        this.tableProductions = productions.getTableProductions();
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

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();

        for (Variable variable : tableProductions.keySet()) {
            List<GrammarString> grammarStrings = tableProductions.get(variable);
            stringBuilder
                    .append(variable)
                    .append(" -> ");
            for (GrammarString grammarString : grammarStrings) {
                for (GrammarUnit grammarUnit : grammarString.getGrammarUnits()) {
                    stringBuilder.append(grammarUnit);
                }

                stringBuilder.append(" | ");
            }
            stringBuilder.delete(stringBuilder.length()-3, stringBuilder.length());
            stringBuilder.append("\n");
        }
        return "\n" +stringBuilder.toString().trim();
    }
}
