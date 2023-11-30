package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.FA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.StringSymbols;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import java.util.Set;

@AllArgsConstructor
public class Language {
    private FA automate;

    public boolean isValidString(StringSymbols stringSymbols) {
        State currentState = automate.getInitialState();
        for (Symbol symbol : stringSymbols.getSymbols()) {
            State transitionState = (State) automate.getTransitionFunction().transition(currentState, symbol);
            if (transitionState != null) {
                currentState = transitionState;
            } else {
                return false;
            }
        }
        return containsState(currentState, automate.getFinalStates());
    }

    private boolean containsState(State state, Set<State> states) {
        return states.stream().anyMatch(s -> s.equals(state));
    }
}
