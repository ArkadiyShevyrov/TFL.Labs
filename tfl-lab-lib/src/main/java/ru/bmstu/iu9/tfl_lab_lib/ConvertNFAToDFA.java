package ru.bmstu.iu9.tfl_lab_lib;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.*;
import java.util.*;

@UtilityClass
public class ConvertNFAToDFA {
    public static DFA convert(NFA nfa) {
        Set<Symbol> symbols = nfa.getSymbols();
        Symbol epsilon = getEpsilon(symbols);
        Set<State> initialDFAState = getInitialDFAState(nfa, epsilon);

        Set<Set<State>> dfaStates = new HashSet<>();
        dfaStates.add(initialDFAState);

        Map<Set<State>, Map<Symbol, Set<State>>> tableTransition = new HashMap<>();

        Queue<Set<State>> unprocessedDFAStates = new LinkedList<>();
        unprocessedDFAStates.add(initialDFAState);
        while (!unprocessedDFAStates.isEmpty()) {
            Set<State> currentDFAState = unprocessedDFAStates.poll();
            Map<Symbol, Set<State>> map = new HashMap<>();
            for (Symbol symbol : symbols) {
                Set<State> nextState = new HashSet<>();
                for (State nfaState : currentDFAState) {
                    Set<State> transitionState = nfa.getTransitionFunction().transition(nfaState, symbol);
                    nextState.addAll(epsilonClosure(nfa, transitionState, epsilon));
                }
                if (!dfaStates.contains(nextState)) {
                    unprocessedDFAStates.add(nextState);
                    dfaStates.add(nextState);
                }
                map.put(symbol, nextState);
            }
            tableTransition.put(currentDFAState, map);
        }

        Set<Set<State>> dfaFinalStates = new HashSet<>();
        for (Set<State> dfaState : dfaStates) {
            for (State nfaState : dfaState) {
                if (nfa.getFinalStates().contains(nfaState)) {
                    dfaFinalStates.add(dfaState);
                    break;
                }
            }
        }

        Map<Set<State>, State> repl = new HashMap<>();
        for (Set<State> states : dfaStates) {
            repl.put(states, new State());
        }

        Set<State> convertState = new HashSet<>();
        for (Set<State> states : dfaStates) {
            convertState.add(repl.get(states));
        }

        Map<State, Map<Symbol, State>> convertedTableTransition = new HashMap<>();
        for (Set<State> key : tableTransition.keySet()) {
            Map<Symbol, Set<State>> symbolSetMap = tableTransition.get(key);
            Map<Symbol, State> convertedSymbolSetMap = new HashMap<>();
            for (Symbol keyS : symbolSetMap.keySet()) {
                Set<State> states = symbolSetMap.get(keyS);
                convertedSymbolSetMap.put(keyS, repl.get(states));
            }
            convertedTableTransition.put(repl.get(key), convertedSymbolSetMap);
        }

        Set<State> convertFinalStates = new HashSet<>();
        for (Set<State> states : dfaFinalStates) {
            convertFinalStates.add(repl.get(states));
        }

        State convertInitState = nfa.getInitialState();

        TransitionFunctionDFA transitionFunctionDFA = new TransitionFunctionDFA(convertedTableTransition);

        return new DFA(convertState, symbols, convertInitState, convertFinalStates, transitionFunctionDFA);
    }

    private static Set<State> getInitialDFAState(NFA nfa, Symbol epsilon) {
        Set<State> initialNFAState = new HashSet<>();
        initialNFAState.add(nfa.getInitialState());
        return epsilonClosure(nfa, initialNFAState, epsilon);
    }

    private static Symbol getEpsilon(Set<Symbol> symbols) {
        for (Symbol symbol : symbols) {
            if (symbol.getType() == Symbol.Type.EPSILON) {
                return symbol;
            }
        }
        return null;
    }

    private static Set<State> epsilonClosure(NFA nfa, Set<State> states, Symbol epsilon) {
        Set<State> closure = new HashSet<>();
        Stack<State> stack = new Stack<>();
        stack.addAll(states);
        while (!stack.isEmpty()) {
            State currentState = stack.pop();
            Set<State> epsilonTransitions = nfa.getTransitionFunction().transition(currentState, epsilon);
            if (epsilonTransitions != null) {
                for (State epsilonState : epsilonTransitions) {
                    if (!closure.contains(epsilonState)) {
                        closure.add(epsilonState);
                        stack.push(epsilonState);
                    }
                }
            }
        }
        return closure;
    }

}
