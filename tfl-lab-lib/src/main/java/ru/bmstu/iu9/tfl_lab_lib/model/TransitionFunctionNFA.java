package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.AllArgsConstructor;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

@AllArgsConstructor
public class TransitionFunctionNFA implements TransitionFunction {

    private Map<State, Map<Symbol, Set<State>>> tableTransition;

    private Symbol epsilon;

    public TransitionFunctionNFA(Map<State, Map<Symbol, Set<State>>> tableTransition) {
        this.tableTransition = tableTransition;
    }

    @Override
    public Set<State> transition(State state, Symbol symbol) {
        return tableTransition.get(state).get(symbol);
    }

    @Override
    public Set<State> advancedTransition(State state, StringSymbols symbols) {
        if (symbols == null) {
            Set<State> states = new HashSet<>();
            states.add(state);
            return states;
        }
        Set<State> pStates = advancedTransition(state, symbols.getAllExpectLast());
        Set<State> rStates = new HashSet<>();
        for (State pState : pStates) {
            Set<State> transition = transition(pState, symbols.getLast());
            rStates.addAll(transition);
        }
        Set<State> resultStates = new HashSet<>();
        for (State rState : rStates) {
            resultStates.addAll(epsilonClosure(rState));
        }
        return resultStates;
    }


    public Set<State> epsilonClosure(State state) {
        Set<State> states = new HashSet<>();
        states.add(state);
        Set<State> eStates = transition(state, epsilon);
        if (eStates != null) {
            for (State eState : eStates) {
                states.addAll(epsilonClosure(eState));
            }
        }
        return states;
    }
}
