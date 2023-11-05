package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

@AllArgsConstructor
public class TransitionFunctionNFA implements TransitionFunction {

    private Map<State, Map<Symbol, Set<State>>> tableTransition;

    @Override
    public Set<State> transition(State state, Symbol symbol) {
        return tableTransition.get(state).get(symbol);
    }

    @Override
    public Set<State> advancedTransition(State state, StringSymbols symbols) {
        if (symbols == null) {
            Set<State> states = new HashSet<>();
            states.add(state);
            return states;
        }
        Set<State> resultStates = new HashSet<>();
        Set<State> statesAT = advancedTransition(state, symbols.getAllExpectLast());
        for (State stateAT : statesAT) {
            Set<State> transition = transition(stateAT, symbols.getLast());
            if (!transition.isEmpty()) {
                resultStates.addAll(transition);
            }
        }
        return resultStates;
    }
}
