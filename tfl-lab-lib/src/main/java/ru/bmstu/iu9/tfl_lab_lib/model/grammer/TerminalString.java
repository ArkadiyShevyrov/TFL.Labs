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
public class TerminalString {
    private List<Terminal> terminals;

    public TerminalString(String string) {
        List<Terminal> terminals = new ArrayList<>();
        for (char c : string.toCharArray()) {
            terminals.add(new Terminal(String.valueOf(c)));
        }
        this.terminals = terminals;
    }

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

    @Override
    public String toString() {
        return Arrays.toString(terminals.toArray());
    }
}
