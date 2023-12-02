package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.StringSymbols;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import java.util.ArrayList;
import java.util.List;

@Getter
@AllArgsConstructor
public class TerminalString {
    private List<Terminal> terminals;

    public TerminalString substring(int index) {
        List<Terminal> newTerminals = new ArrayList<>();
        for (int i = index; i < this.terminals.size(); i++) {
            newTerminals.add(this.terminals.get(i));
        }
        return new TerminalString(newTerminals);
    }

    public Terminal get(int index) {
        return terminals.get(index);
    }

    public Terminal getFirst() {
        if (terminals.size() < 1) {
            return null;
        }
        return terminals.get(0);
    }

    public int length() {
        return terminals.size();
    }
}
