package ru.bmstu.iu9.tfl_lab_lib.automaton;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.Set;

@Getter
@AllArgsConstructor
public class NFA implements FA {
    private Set<State> states;
    private Set<Symbol> symbols;
    private State initialState;
    private Set<State> finalStates;
    private TransitionFunctionNFA transitionFunction;
}
