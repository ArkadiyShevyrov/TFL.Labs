package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;

@Getter
@AllArgsConstructor
public class Symbol {
    private String string;
    private Type type;
    private Regex regex;

    public Symbol(Type type) {
        this.type = type;
    }

    public Symbol(String string) {
        this.string = string;
        this.type = Type.SYMBOL;
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

    public enum Type {
        SYMBOL,
        EPSILON,
        REGEX
    }
}
