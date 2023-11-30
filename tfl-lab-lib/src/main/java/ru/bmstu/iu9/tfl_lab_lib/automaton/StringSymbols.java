package ru.bmstu.iu9.tfl_lab_lib.automaton;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.ArrayList;
import java.util.List;

@Getter
@AllArgsConstructor
public class StringSymbols {
    private List<Symbol> symbols;

    public StringSymbols(String string) {
        List<Symbol> symbols = new ArrayList<>();
        for (char c : string.toCharArray()) {
            symbols.add(new Symbol(String.valueOf(c)));
        }
        this.symbols = symbols;
    }

    public StringSymbols substring(int startIndex, int endIndex) {
        List<Symbol> newSymbols = new ArrayList<>();
        for (int i = startIndex; i < endIndex; i++) {
            newSymbols.add(this.symbols.get(i));
        }
        return new StringSymbols(newSymbols);
    }

    public StringSymbols substring(int index) {
        List<Symbol> newSymbols = new ArrayList<>();
        for (int i = index; i < this.symbols.size(); i++) {
            newSymbols.add(this.symbols.get(i));
        }
        return new StringSymbols(newSymbols);
    }

    public Symbol getLast() {
        if (symbols.size() < 1) {
            return null;
        }
        return symbols.get(symbols.size() - 1);
    }

    public StringSymbols getAllExpectLast() {
        if (symbols.size() < 2) {
            return null;
        }
        return this.substring(symbols.size() - 2);
    }
}
