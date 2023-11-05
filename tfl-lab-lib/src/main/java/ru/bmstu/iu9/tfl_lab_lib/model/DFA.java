package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import java.util.List;
import java.util.Set;

@AllArgsConstructor
public class DFA {
    private Set<State> states;
    private Set<Symbol> symbols;
    private State initialState;
    private Set<State> finalStates;
    private TransitionFunctionDFA transitionFunction;

    public boolean isValidString(List<Symbol> symbols) {
        State currentState = this.initialState;
        for (Symbol symbol : symbols) {
            State transitionState = this.transitionFunction.transition(currentState, symbol);
            if (transitionState != null) {
                currentState = transitionState;
            } else {
                return false;
            }
        }
        return containsState(currentState, this.finalStates);
    }

    private boolean containsState(State state, Set<State> states) {
        return states.stream().anyMatch(s -> s.equals(state));
    }
}