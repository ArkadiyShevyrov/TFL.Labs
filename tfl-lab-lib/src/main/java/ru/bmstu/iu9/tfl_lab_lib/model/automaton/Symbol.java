package ru.bmstu.iu9.tfl_lab_lib.model.automaton;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import java.io.Serializable;

@Getter
@AllArgsConstructor
@EqualsAndHashCode
public class Symbol implements Serializable, Comparable<Symbol> {
    public static Symbol epsilon = new Symbol(Type.EPSILON);
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

    @Override
    public int compareTo(Symbol other) {
        return Integer.compare(this.hashCode(), other.hashCode());

    }

    public enum Type {
        SYMBOL,
        EPSILON,
        REGEX,
        VALUE
    }
}
