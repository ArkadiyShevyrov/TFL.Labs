package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import java.io.Serializable;

@Getter
@AllArgsConstructor
@EqualsAndHashCode
public class Symbol implements Serializable {
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

    public Symbol(Type type, Regex regex) {
        this.type = type;
        this.regex = regex;
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
