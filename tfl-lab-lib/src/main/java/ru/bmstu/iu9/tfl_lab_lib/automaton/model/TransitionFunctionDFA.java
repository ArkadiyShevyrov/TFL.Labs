package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@Getter
@AllArgsConstructor
public class TransitionFunctionDFA implements TransitionFunction, Serializable {

    private Map<State, Map<Symbol, State>> tableTransition;

    @Override
    public State transition(State state, Symbol symbol) {
        return tableTransition.get(state).get(symbol);
    }

    public State advancedTransition(State state, StringSymbols symbols) {
        return transition(advancedTransition(state, symbols.getAllExpectLast()), symbols.getLast());
    }


    public void putToTable(State stateStart, Symbol symbol, State stateEnd) {
        Map<Symbol, State> oldMap = tableTransition.get(stateStart);
        Map<Symbol, State> newMap = Objects.requireNonNullElseGet(oldMap, HashMap::new);
        newMap.put(symbol, stateEnd);
        tableTransition.put(stateStart, newMap);
    }
}
