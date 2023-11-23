package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.*;

@Getter
@AllArgsConstructor
public class TransitionFunctionNFA implements TransitionFunction {

    private Map<State, Map<Symbol, Set<State>>> tableTransition;

    private Symbol epsilon = new Symbol(Symbol.Type.EPSILON);

    public TransitionFunctionNFA(Map<State, Map<Symbol, Set<State>>> tableTransition) {
        this.tableTransition = tableTransition;
    }

    public TransitionFunctionNFA() {
        this.tableTransition = new HashMap<>();
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

    public void putToTable(State stateStart, Symbol symbol, Set<State> stateEnd) {
        Map<Symbol, Set<State>> oldMap = tableTransition.get(stateStart);
        Map<Symbol, Set<State>> newMap = Objects.requireNonNullElseGet(oldMap, HashMap::new);
        Set<State> states = newMap.get(symbol);
        if (states == null) {
            newMap.put(symbol, stateEnd);
        } else {
            states.addAll(stateEnd);
        }
        tableTransition.put(stateStart, newMap);
    }

    public void putAll(TransitionFunctionNFA transitionFunctionNFA) {
        tableTransition.putAll(transitionFunctionNFA.getTableTransition());
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();

        for (Map.Entry<State, Map<Symbol, Set<State>>> entry : tableTransition.entrySet()) {
            State key = entry.getKey();
            Map<Symbol, Set<State>> value = entry.getValue();

            for (Map.Entry<Symbol, Set<State>> innerEntry : value.entrySet()) {
                Symbol innerKey = innerEntry.getKey();
                Set<State> innerValue = innerEntry.getValue();

                stringBuilder.append(key).append(" -> ").append(innerKey).append(" -> ").append(innerValue).append("\n");
            }
        }
        return "\n" +stringBuilder.toString().trim();
    }
}
