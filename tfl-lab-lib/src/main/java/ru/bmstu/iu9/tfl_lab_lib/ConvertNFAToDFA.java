package ru.bmstu.iu9.tfl_lab_lib;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.*;
import java.util.*;

@UtilityClass
public class ConvertNFAToDFA {
    public DFA convert(NFA nfa) {
        Set<Symbol> dfaSymbols = nfa.getSymbols();

        State dfaInitialState = getDfaInitialState(nfa);

        TransitionFunctionDFA transitionFunctionDFA = getStateMapMap(nfa, dfaSymbols, dfaInitialState);

        Set<State> dfaStates = transitionFunctionDFA.getTableTransition().keySet();

        Set<State> dfaFinalStates = getDfaFinalStates(nfa, dfaStates);

        return new DFA(dfaStates, dfaSymbols, dfaInitialState, dfaFinalStates, transitionFunctionDFA);
    }

    private State getDfaInitialState(NFA nfa) {
        return new State(new HashSet<>(Collections.singletonList(nfa.getInitialState())));
    }

    private TransitionFunctionDFA getStateMapMap(NFA nfa, Set<Symbol> dfaSymbols, State dfaInitialState) {
        Set<State> dfaStates = new HashSet<>();
        Map<State, Map<Symbol, State>> dfaTableTransition = new HashMap<>();
        Queue<State> unprocessedDFAStates = new LinkedList<>();
        unprocessedDFAStates.add(dfaInitialState);
        while (!unprocessedDFAStates.isEmpty()) {
            State currentDFAState = unprocessedDFAStates.poll();
            Map<Symbol, State> map = new HashMap<>();
            for (Symbol symbol : dfaSymbols) {
                Set<State> subStates = new HashSet<>();
                if (currentDFAState.getValue().getType() == StateValue.Type.SET_STATE) {
                    Set<State> subCurrentStates = currentDFAState.getValue().getSetState();
                    for (State subCurrentState : subCurrentStates) {
                        Set<State> transitionState = nfa.getTransitionFunction().transition(subCurrentState, symbol);
                        subStates.addAll(epsilonClosure(nfa, transitionState));
                    }
                }
                State nextState = newStateFromSubStates(dfaStates, subStates);
                if (!dfaStates.contains(nextState)) {
                    unprocessedDFAStates.add(nextState);
                    dfaStates.add(nextState);
                }
                map.put(symbol, nextState);
            }
            dfaTableTransition.put(currentDFAState, map);
        }
        return new TransitionFunctionDFA(dfaTableTransition);
    }

    private Set<State> getDfaFinalStates(NFA nfa, Set<State> dfaStates) {
        Set<State> dfaFinalStates = new HashSet<>();
        for (State dfaState : dfaStates) {
            if (dfaState.getValue().getType() == StateValue.Type.SET_STATE) {
                for (State subState : dfaState.getValue().getSetState()) {
                    if (nfa.getFinalStates().contains(subState)) {
                        dfaFinalStates.add(dfaState);
                        break;
                    }
                }
            }
        }
        return dfaFinalStates;
    }

    private State newStateFromSubStates(Set<State> states, Set<State> subStates) {
        for (State state : states) {
            if (state.getValue().getSetState().equals(subStates)) {
                return state;
            }
        }
        return new State(subStates);
    }


    private Symbol getEpsilon(Set<Symbol> symbols) {
        for (Symbol symbol : symbols) {
            if (symbol.getType() == Symbol.Type.EPSILON) {
                return symbol;
            }
        }
        return null;
    }

    private Set<State> epsilonClosure(NFA nfa, Set<State> states) {
        Symbol epsilon = getEpsilon(nfa.getSymbols());
        Set<State> closure = new HashSet<>(states);
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
