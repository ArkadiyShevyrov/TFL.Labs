package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;

@Getter
@AllArgsConstructor
@NoArgsConstructor
public class Symbol {
    private String value;
    private Type type;

    public enum Type {
        SYMBOL,
        EPSILON
    }

    @Override
    public String toString() {
        return value;
    }
}
