package ru.bmstu.iu9.tfl_lab_lib.language;

import ru.bmstu.iu9.tfl_lab_lib.automaton.model.FA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.State;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.StringSymbols;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.Symbol;
import java.util.Set;

public class Language {
    private FA automate;

//    public boolean isValidString(StringSymbols stringSymbols) {
//        State currentState = ;
//        for (Symbol symbol : symbols) {
//            State transitionState = this.transitionFunction.transition(currentState, symbol);
//            if (transitionState != null) {
//                currentState = transitionState;
//            } else {
//                return false;
//            }
//        }
//        return containsState(currentState, this.finalStates);
//    }
//
//    private boolean containsState(State state, Set<State> states) {
//        return states.stream().anyMatch(s -> s.equals(state));
//    }
}
