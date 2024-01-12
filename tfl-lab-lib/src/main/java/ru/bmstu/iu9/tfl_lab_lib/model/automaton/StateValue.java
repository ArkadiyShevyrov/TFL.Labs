package ru.bmstu.iu9.tfl_lab_lib.model.automaton;

import lombok.EqualsAndHashCode;
import lombok.Getter;
import lombok.Setter;
import java.io.Serializable;
import java.util.Arrays;
import java.util.Set;

@Getter
@Setter
@EqualsAndHashCode
public class StateValue implements Serializable {
    private Type type;

    private Set<State> setState;

    private String string;

    public StateValue(Type type, Set<State> setState) {
        if (type == Type.SET_STATE) {
            this.type = type;
            this.setState = setState;
        }
    }

    public StateValue(Type type, String string) {
        if (type == Type.STRING) {
            this.type = type;
            this.string = string;
        }
    }

    public enum Type {
        SET_STATE,
        STRING
    }

    @Override
    public String toString() {
        switch (type) {
            case STRING -> {
                return string;
            }
            case SET_STATE -> {
                return Arrays.deepToString(setState.toArray());
            }
            default -> {
                return "";
            }
        }
    }
}
