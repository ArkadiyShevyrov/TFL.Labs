package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;

@Getter
@AllArgsConstructor
@NoArgsConstructor
public class Symbol {
    private String string;
    private Type type;
    private Regex regex;

    public enum Type {
        SYMBOL,
        EPSILON,
        REGEX
    }

    @Override
    public String toString() {
        switch (type) {
            case SYMBOL -> {
                return string;
            }
            case REGEX -> {
                return regex.toString();
            }
            case EPSILON -> {
                return "ε";
            }
            default -> {
                return null;
            }
        }
    }
}
