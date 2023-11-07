package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.ToString;

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
