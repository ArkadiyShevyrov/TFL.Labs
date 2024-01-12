package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;

@Getter
@AllArgsConstructor
@EqualsAndHashCode
public class Variable implements GrammarUnit {
    String name;

    @Override
    public String toString() {
        return name;
    }
}
