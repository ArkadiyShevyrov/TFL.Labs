package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;

@Getter
@AllArgsConstructor
@NoArgsConstructor
public class Symbol {
    private Type type;

    public enum Type {
        SYMBOL,
        EPSILON
    }
}
