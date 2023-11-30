package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import lombok.experimental.UtilityClass;
import org.apache.commons.lang3.SerializationUtils;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.DFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.TransitionFunctionDFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.optimize.OptimizeRegexForEpsilonAndEmpty;
import java.util.*;

@UtilityClass
public class ConvertDFAToRegex {

    public Regex convert(DFA dfa) {
        List<Regex> regexes = new ArrayList<>();
        Set<State> finalStates = dfa.getFinalStates();
        for (State finalState : finalStates) {
            Regex regex = exclusion(SerializationUtils.clone(dfa), SerializationUtils.clone(dfa.getTransitionFunction()), finalState);
            regexes.add(regex);
        }
        return OptimizeRegexForEpsilonAndEmpty.optimize(combinateRegex(regexes));
    }

    private Regex combinateRegex(List<Regex> regexes) {
        if (regexes.size() == 0) {
            return new Regex(Regex.Type.EMPTY);
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
        State initialState = dfa.getInitialState();
        Set<State> statesOtherInitialAndFinal = getStatesOtherInitialAndFinal(states, initialState, finalState);
        Map<State, Map<Symbol, State>> tableTransition = transitionFunction.getTableTransition();

        for (State state : statesOtherInitialAndFinal) {
            Set<State> previousStates = getPreviousStates(tableTransition, state);
            Set<State> nextStates = getNextStates(tableTransition, state);
            if (nextStates.size() == 0) {
                for (State prev : previousStates) {
                    removeTransitions(tableTransition, prev, state);
                }
            }
            for (State prev : previousStates) {
                for (State next : nextStates) {
                    Regex prevNext = getTransitionRegex(
                            SerializationUtils.clone(transitionFunction).getTableTransition(), prev, next);
                    removeTransitions(tableTransition, prev, next);
                    Regex prevState = getTransitionRegex(
                            SerializationUtils.clone(transitionFunction).getTableTransition(), prev, state);
                    Regex stateNext = getTransitionRegex(
                            SerializationUtils.clone(transitionFunction).getTableTransition(), state, next);
                    Regex stateState = getTransitionRegex(
                            SerializationUtils.clone(transitionFunction).getTableTransition(), state, state);
                    Regex regex = OptimizeRegexForEpsilonAndEmpty.optimize(new Regex(
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
                    ));
                    if (regex.getType() == Regex.Type.EMPTY) {
                        continue;
                    }
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
        if (initialState.equals(finalState)) {
            return OptimizeRegexForEpsilonAndEmpty.optimize(new Regex(Regex.Type.ASTERISK, getTransitionRegex(
                    SerializationUtils.clone(transitionFunction).getTableTransition(), initialState, initialState)));
        }
        Regex initInit = getTransitionRegex(
                SerializationUtils.clone(transitionFunction).getTableTransition(), initialState, initialState);
        Regex finalFinal = getTransitionRegex(
                SerializationUtils.clone(transitionFunction).getTableTransition(), finalState, finalState);
        Regex initFinal = getTransitionRegex(
                SerializationUtils.clone(transitionFunction).getTableTransition(), initialState, finalState);
        Regex finalInit = getTransitionRegex(
                SerializationUtils.clone(transitionFunction).getTableTransition(), finalState, initialState);
        return OptimizeRegexForEpsilonAndEmpty.optimize(new Regex(
                Regex.Type.CONCAT,
                new Regex(
                        Regex.Type.ASTERISK,
                        new Regex(
                                Regex.Type.OR,
                                initInit,
                                new Regex(
                                        Regex.Type.CONCAT,
                                        initFinal,
                                        new Regex(
                                                Regex.Type.CONCAT,
                                                new Regex(
                                                        Regex.Type.ASTERISK,
                                                        finalFinal
                                                ),
                                                finalInit
                                        )
                                )
                        )
                ),
                new Regex(
                        Regex.Type.CONCAT,
                        initFinal,
                        new Regex(
                                Regex.Type.ASTERISK,
                                finalFinal
                        )
                )
        ));
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
