package ru.bmstu.iu9.tfl_lab_lib.model.automaton;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import lombok.NoArgsConstructor;
import java.io.Serializable;
import java.util.Set;

@Getter
@AllArgsConstructor
@NoArgsConstructor
@EqualsAndHashCode
public class State implements Serializable {
    private StateValue value;

    public State(String value) {
        this.value = new StateValue(StateValue.Type.STRING, value);
    }

    public State(Set<State> setState) {
        this.value = new StateValue(StateValue.Type.SET_STATE, setState);
    }

    @Override
    public String toString() {
        return value.toString();
    }
}
