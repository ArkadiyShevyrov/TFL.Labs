package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;

@Getter
@AllArgsConstructor
@EqualsAndHashCode
public class Terminal implements GrammarUnit {
    private String value;
    private Type type;

    public Terminal(String value) {
        this.type = Type.STRING;
        this.value = value;
    }

    public Terminal(Type type) {
        this.type = type;
    }

    @Override
    public String toString() {
        return value;
    }

    public enum Type {
        STRING,
        EPSILON
    }
}
