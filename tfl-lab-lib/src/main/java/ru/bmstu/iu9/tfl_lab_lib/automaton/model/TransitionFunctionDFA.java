package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.Map;

@Getter
@AllArgsConstructor
public class TransitionFunctionDFA implements TransitionFunction {

    private Map<State, Map<Symbol, State>> tableTransition;

    @Override
    public State transition(State state, Symbol symbol) {
        return tableTransition.get(state).get(symbol);
    }

    public State advancedTransition(State state, StringSymbols symbols) {
        return transition(advancedTransition(state, symbols.getAllExpectLast()), symbols.getLast());
    }
}
