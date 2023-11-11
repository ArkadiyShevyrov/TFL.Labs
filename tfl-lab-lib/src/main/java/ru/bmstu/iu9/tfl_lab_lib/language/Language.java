package ru.bmstu.iu9.tfl_lab_lib.language;

import lombok.AllArgsConstructor;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.FA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.State;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.StringSymbols;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.Symbol;
import java.util.Set;

@AllArgsConstructor
public class Language {
    private FA automate;

    public boolean isValidString(StringSymbols stringSymbols) {
        State currentState = automate.getInitialState();
        for (Symbol symbol : stringSymbols.getSymbols()) {
            State transitionState = automate.getTransitionFunction().transition(currentState, symbol);
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
