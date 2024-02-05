package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import lombok.experimental.UtilityClass;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.lang3.SerializationUtils;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.TransitionFunctionNFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.Optimize;
import ru.bmstu.iu9.tfl_lab_lib.utils.RegexUtils;

import java.util.*;

@Slf4j
@UtilityClass
public class ConvertNFAToRegex {
    private final Regex empty = new Regex(Regex.Type.EMPTY);

    public Regex convert1(NFA nfa) {

        NFA nfa1 = addInitialState(nfa);
        NFA nfa2 = addFinalState(nfa1);

        Set<State> removingStates = nfa2.getStates();
        removingStates.remove(nfa2.getInitialState());
        removingStates.remove(nfa2.getFinalStates().stream().toList().get(0));

        NFA currentNFA = getNfaZero(nfa2, removingStates);

        log.info(nfa2.toString());
        return getTransitionRegex(currentNFA.getTransitionFunction().getTableTransition(), currentNFA.getInitialState(), currentNFA.getFinalStates().stream().toList().get(0));
    }

    public Regex convert2(NFA nfa) {

        NFA nfa1 = addInitialState(nfa);
        NFA nfa2 = addFinalState(nfa1);

        Set<State> removingStates = nfa2.getStates();
        removingStates.remove(nfa2.getInitialState());
        removingStates.remove(nfa2.getFinalStates().stream().toList().get(0));

        List<NFA> currentNFA = getNfaALL(nfa2, removingStates);

        List<Regex> regexes = new ArrayList<>();
        for (NFA nfa3 : currentNFA) {
            regexes.add(getTransitionRegex(nfa3.getTransitionFunction().getTableTransition(), nfa3.getInitialState(), nfa3.getFinalStates().stream().toList().get(0)));
        }

        regexes.sort(Comparator.comparingInt(ConvertNFAToRegex::countW));

        log.info(Arrays.deepToString(regexes.toArray()));

        return new Regex(regexes.get(0).toString());
    }

    private int countW(Regex regexes) {
        String onlyLetters = regexes.toString().replaceAll("[^a-zA-Z0-9]", "");
        return onlyLetters.length();
    }

    private List<NFA> getNfaALL(NFA nfa2, Set<State> removingStates) {
        List<List<State>> allList = new ArrayList<>();
        for (State state : removingStates) {
            for (State state1 : removingStates) {
                if (state.equals(state1)) {
                    continue;
                }
                List<State> list = new ArrayList<>();
                list.add(state);
                list.add(state1);
                for (State state2 : removingStates) {
                    if (state.equals(state2) || state1.equals(state2)) {
                        continue;
                    }
                    list.add(state2);
                }
                allList.add(list);
            }
        }

        List<NFA> nfaAll = new ArrayList<>();
        for (List<State> list : allList) {
            NFA currentNFA = SerializationUtils.clone(nfa2);
            for (State removingState : list) {
                currentNFA = removeState(currentNFA, removingState);
            }
            nfaAll.add(currentNFA);
        }

        return nfaAll;
    }

    private static NFA getNfaZero(NFA nfa2, Set<State> removingStates) {
        NFA currentNFA = nfa2;
        List<State> list = new ArrayList<>(removingStates.stream().toList());
        NFA finalCurrentNFA = currentNFA;
        Collections.sort(list, Comparator.comparingInt(s -> countOut(s, finalCurrentNFA)));
        log.info("\nList Removing  "+Arrays.deepToString(list.toArray()));
        for (State removingState : list) {
            currentNFA = removeState(currentNFA, removingState);
        }
        return currentNFA;
    }

    private int countOut(State state, NFA currentNFA) {
        TransitionFunctionNFA transitionFunction = currentNFA.getTransitionFunction();
        Map<State, Map<Symbol, Set<State>>> tableTransition = transitionFunction.getTableTransition();
        Map<Symbol, Set<State>> symbolSetMap = tableTransition.get(state);
        Set<State> statesNext = new HashSet<>();
        for (Symbol symbol : symbolSetMap.keySet()) {
            Set<State> states = symbolSetMap.get(symbol);
            statesNext.addAll(states);
        }
        return statesNext.size();
    }

    private NFA addInitialState(NFA nfa) {
        Set<State> states = nfa.getStates();
        Set<Symbol> symbols = nfa.getSymbols();
        State initialState = new State(nfa.getInitialState() + "0");
        states.add(initialState);
        Set<State> finalStates = nfa.getFinalStates();
        TransitionFunctionNFA transitionFunction = nfa.getTransitionFunction();
        transitionFunction.putToTable(initialState, Symbol.epsilon, nfa.getInitialState());
        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA addFinalState(NFA nfa) {
        Set<State> states = nfa.getStates();
        Set<Symbol> symbols = nfa.getSymbols();
        State initialState = nfa.getInitialState();
        Set<State> finalStates = new HashSet<>();
        State newFinalState = new State(nfa.getFinalStates());
        finalStates.add(newFinalState);
        states.add(newFinalState);
        TransitionFunctionNFA transitionFunction = nfa.getTransitionFunction();
        for (State prevFinalState : nfa.getFinalStates()) {
            transitionFunction.putToTable(prevFinalState, Symbol.epsilon, newFinalState);
        }
        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA removeState(NFA nfa, State state) {
        TransitionFunctionNFA transitionFunction = nfa.getTransitionFunction();
        Map<State, Map<Symbol, Set<State>>> tableTransition = transitionFunction.getTableTransition();

        Set<State> prevStates = getPrevStates(tableTransition, state);
        Set<State> nextStates = getNextStates(tableTransition, state);


        for (State prev : prevStates) {
            for (State next : nextStates) {
//                if (prev.equals(next)) {
//                    continue;
//                }
                Regex prevNext = getTransitionRegex(transitionFunction.getTableTransition(), prev, next);
                removeTransitions(tableTransition, prev, next);
                Regex prevState = getTransitionRegex(transitionFunction.getTableTransition(), prev, state);
                Regex stateNext = getTransitionRegex(transitionFunction.getTableTransition(), state, next);
                Regex stateState = getTransitionRegex(transitionFunction.getTableTransition(), state, state);
                Regex regex = Optimize.optimizeRegexForEpsilonAndEmpty(new Regex(
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
        for (State prev : prevStates) {
            for (State next : nextStates) {
                removeTransitions(tableTransition, prev, state);
                removeTransitions(tableTransition, state, next);
                removeTransitions(tableTransition, state, state);
            }
        }
        return nfa;
    }


    private static Set<State> getPrevStates(Map<State, Map<Symbol, Set<State>>> tableTransition, State s) {
        Set<State> previousStates = new HashSet<>();
        for (State key : tableTransition.keySet()) {
            Map<Symbol, Set<State>> transitions = tableTransition.get(key);
            for (Symbol symbol : transitions.keySet()) {
                Set<State> states = transitions.get(symbol);
                if (states.contains(s)) {
                    previousStates.add(key);
                }
            }
        }
        previousStates.remove(s);
        return previousStates;
    }

    private static Set<State> getNextStates(Map<State, Map<Symbol, Set<State>>> tableTransition, State s) {
        Set<State> nextStates = new HashSet<>();
        if (tableTransition.containsKey(s)) {
            Map<Symbol, Set<State>> transitions = tableTransition.get(s);
            for (Symbol symbol : transitions.keySet()) {
                Set<State> c = transitions.get(symbol);
                nextStates.addAll(c);
            }
        }
        nextStates.remove(s);
        return nextStates;
    }

    private static Regex getTransitionRegex(Map<State, Map<Symbol, Set<State>>> tableTransition, State one, State two) {
        Map<Symbol, Set<State>> transitionMap = tableTransition.get(one);
        Set<Symbol> symbols = transitionMap.keySet();
        Set<Symbol> currentSymbols = new HashSet<>();
        for (Symbol symbol : symbols) {
            Set<State> states = transitionMap.get(symbol);
            for (State state : states) {
                if (state.equals(two)) {
                    currentSymbols.add(symbol);
                }
            }
        }
        if (currentSymbols.isEmpty()) {
            return empty;
        }
        List<Regex> regexes = new ArrayList<>();
        for (Symbol symbol : currentSymbols) {
            switch (symbol.getType()) {
                case EPSILON -> regexes.add(new Regex(Regex.Type.EPSILON));
                case REGEX -> regexes.add(symbol.getRegex());
                case SYMBOL -> regexes.add(new Regex(Regex.Type.SYMBOL, symbol.getString()));
            }
        }
        return RegexUtils.combinateRegex(regexes);
    }

    private void removeTransitions(Map<State, Map<Symbol, Set<State>>> tableTransition, State fromState, State toState) {
        Map<Symbol, Set<State>> transitionsFromState = tableTransition.get(fromState);
        if(transitionsFromState.isEmpty()) {
            return;
        }
        Set<Symbol> symbolsForRemove = new HashSet<>();
        for (Symbol symbol : transitionsFromState.keySet()) {
            Set<State> states = transitionsFromState.get(symbol);
            if (states.contains(toState)) {
                if (states.size() == 1) {
                    symbolsForRemove.add(symbol);
                }
                if (states.size() > 1) {
                    states.remove(toState);
                    transitionsFromState.put(symbol, states);
                }
            }
        }
        for (Symbol symbol: symbolsForRemove) {
            transitionsFromState.remove(symbol);
        }
    }
}
