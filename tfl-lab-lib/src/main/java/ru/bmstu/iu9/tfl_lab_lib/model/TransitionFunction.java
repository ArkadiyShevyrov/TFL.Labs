package ru.bmstu.iu9.tfl_lab_lib.model;

public interface TransitionFunction {
    Object transition(State state, Symbol symbol);

    Object advancedTransition(State state, StringSymbols symbols);
}