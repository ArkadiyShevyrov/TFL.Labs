package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.io.Serializable;
import java.util.Set;

@Getter
@AllArgsConstructor
public class DFA implements FA {
    private Set<State> states;
    private Set<Symbol> symbols;
    private State initialState;
    private Set<State> finalStates;
    private TransitionFunctionDFA transitionFunction;
}