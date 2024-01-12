package ru.bmstu.iu9.tfl_lab_lib.model.automaton;

import java.util.Set;

public interface FA {
    Set<State> getStates();

    Set<Symbol> getSymbols();

    State getInitialState();

    Set<State> getFinalStates();

    TransitionFunction getTransitionFunction();
}
