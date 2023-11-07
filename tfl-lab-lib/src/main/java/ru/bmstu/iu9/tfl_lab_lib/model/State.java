package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import lombok.NoArgsConstructor;
import lombok.ToString;

@AllArgsConstructor
@NoArgsConstructor
public class State {
    private String name;

    @Override
    public String toString() {
        return name;
    }
}
