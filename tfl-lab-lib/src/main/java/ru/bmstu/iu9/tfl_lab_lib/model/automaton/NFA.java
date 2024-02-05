package ru.bmstu.iu9.tfl_lab_lib.model.automaton;

import lombok.AllArgsConstructor;
import lombok.Getter;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Set;

@Getter
@AllArgsConstructor
public class NFA implements FA, Serializable {
    private Set<State> states;
    private Set<Symbol> symbols;
    private State initialState;
    private Set<State> finalStates;
    private TransitionFunctionNFA transitionFunction;

    @Override
    public String toString() {
        String string = "States: \n" +
                Arrays.deepToString(states.stream().sorted().toArray()) + "\n" +
                "Symbols: \n" +
                Arrays.deepToString(symbols.stream().sorted().toArray()) + "\n" +
                "Initial state: \n" +
                initialState + "\n" +
                "Final states: \n" +
                Arrays.deepToString(finalStates.stream().sorted().toArray()) + "\n" +
                "Transition Function NFA: \n" +
                transitionFunction.toString().trim();
        return "\n" + string.trim();
    }
}
