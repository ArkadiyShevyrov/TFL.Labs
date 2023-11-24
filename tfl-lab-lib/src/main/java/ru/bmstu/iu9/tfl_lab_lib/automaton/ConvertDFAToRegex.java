package ru.bmstu.iu9.tfl_lab_lib.automaton;

import lombok.experimental.UtilityClass;
import org.apache.commons.lang3.SerializationUtils;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.*;
import java.util.*;

@UtilityClass
public class ConvertDFAToRegex {

    public Regex convert(DFA dfa) {
        List<Regex> regexes = new ArrayList<>();
        Set<State> finalStates = dfa.getFinalStates();
        for (State finalState : finalStates) {
            Regex regex = exclusion(dfa, SerializationUtils.clone(dfa.getTransitionFunction()), finalState);
            regexes.add(regex);
        }
        return combinateRegex(regexes);
    }

    private Regex combinateRegex(List<Regex> regexes) {
        if (regexes.size() == 0) {
            return null;
        }
        if (regexes.size() == 1) {
            return regexes.get(0);
        }
        Regex res = new Regex(Regex.Type.OR, regexes.get(0));
        Regex current = res;
        for (int i = 1; i < regexes.size(); i++) {
            Regex regex = regexes.get(i);
            if (i == regexes.size() - 1) {
                current.setRight(regex);
                break;
            }
            Regex right = new Regex(Regex.Type.OR, regex);
            current.setRight(right);
            current = right;
        }
        return res;
    }

    private Regex exclusion(DFA dfa, TransitionFunctionDFA transitionFunction, State finalState) {
        Set<State> states = dfa.getStates();
        Set<State> statesOtherInitialAndFinal = getStatesOtherInitialAndFinal(states, dfa.getInitialState(), finalState);
        for (State state : statesOtherInitialAndFinal) {
            Map<State, Map<Symbol, State>> tableTransition = transitionFunction.getTableTransition();
            Set<State> previousStates = getPreviousStates(tableTransition, state);
            Set<State> nextStates = getNextStates(tableTransition, state);
            for (State prev : previousStates) {
                for (State next : nextStates) {
                    Regex prevNext = getTransitionRegex(tableTransition, prev, next);
                    removeTransitions(tableTransition, prev, next);
                    Regex prevState = getTransitionRegex(tableTransition, prev, state);
                    Regex stateNext = getTransitionRegex(tableTransition, state, next);
                    Regex stateState = getTransitionRegex(tableTransition, state, state);
                    Regex regex = new Regex(
                            Regex.Type.OR,
                            prevNext,
                            new Regex(
                                    Regex.Type.CONCAT,
                                    prevState,
                                    new Regex(
                                            Regex.Type.CONCAT,
                                            new Regex(
                                                    Regex.Type.ASTERISK,
                                                    stateState
                                            ),
                                            stateNext
                                    )
                            )
                    );
                    transitionFunction.putToTable(prev, new Symbol(Symbol.Type.REGEX, regex), next);
                }
            }
            for (State prev : previousStates) {
                for (State next : nextStates) {
                    removeTransitions(tableTransition, prev, state);
                    removeTransitions(tableTransition, state, next);
                    removeTransitions(tableTransition, state, state);
                }
            }
        }

        return null;
    }

    private Set<State> getStatesOtherInitialAndFinal(Set<State> states, State initialState, State finalState) {
        states.remove(initialState);
        states.remove(finalState);
        return states;
    }


    public static Set<State> getPreviousStates(Map<State, Map<Symbol, State>> tableTransition, State s) {
        Set<State> previousStates = new HashSet<>();
        for (State key : tableTransition.keySet()) {
            Map<Symbol, State> transitions = tableTransition.get(key);
            if (transitions.containsValue(s)) {
                previousStates.add(key);
            }
        }
        return previousStates;
    }

    private static Set<State> getNextStates(Map<State, Map<Symbol, State>> tableTransition, State s) {
        Set<State> nextStates = new HashSet<>();
        if (tableTransition.containsKey(s)) {
            Map<Symbol, State> transitions = tableTransition.get(s);
            nextStates.addAll(transitions.values());
        }
        return nextStates;
    }

    private static Regex getTransitionRegex(Map<State, Map<Symbol, State>> tableTransition, State one, State two) {
        Map<Symbol, State> transitionMap = tableTransition.get(one);
        Set<Symbol> symbols = transitionMap.keySet();
        symbols.removeIf(symbol -> !transitionMap.get(symbol).equals(two));
        if (symbols.isEmpty()) {
            return new Regex(Regex.Type.EMPTY);
        }
        List<Regex> regexes = new ArrayList<>();
        for (Symbol symbol : symbols) {
            switch (symbol.getType()) {
                case REGEX -> regexes.add(symbol.getRegex());
                case SYMBOL -> regexes.add(new Regex(Regex.Type.SYMBOL, symbol.getString()));
            }
        }
        return combinateRegex(regexes);
    }

    public void removeTransitions(Map<State, Map<Symbol, State>> tableTransition, State fromState, State toState) {
        Map<Symbol, State> transitionsFromState = tableTransition.get(fromState);
        transitionsFromState.entrySet().removeIf(entry -> entry.getValue().equals(toState));
    }
}
