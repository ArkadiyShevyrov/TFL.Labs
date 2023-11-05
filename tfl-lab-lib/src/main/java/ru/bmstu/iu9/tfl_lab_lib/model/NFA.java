package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.List;
import java.util.Set;

@Getter
@AllArgsConstructor
public class NFA {
    private Set<State> states;
    private Set<Symbol> symbols;
    private State initialState;
    private Set<State> finalStates;
    private TransitionFunctionNFA transitionFunction;
}
