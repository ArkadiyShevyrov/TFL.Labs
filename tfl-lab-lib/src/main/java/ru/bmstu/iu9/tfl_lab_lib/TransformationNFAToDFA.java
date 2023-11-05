package ru.bmstu.iu9.tfl_lab_lib;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.DFA;
import ru.bmstu.iu9.tfl_lab_lib.model.NFA;
import ru.bmstu.iu9.tfl_lab_lib.model.State;
import ru.bmstu.iu9.tfl_lab_lib.model.Symbol;
import java.util.*;

@UtilityClass
public class TransformationNFAToDFA {
    public static DFA convertNFAtoDFA(NFA nfa) {
        Set<State> initialDFAState = epsilonClosure(nfa, nfa.getInitialState());
        Set<Set<State>> dfaStates = new HashSet<>();
        dfaStates.add(initialDFAState);
        Set<Symbol> symbols = nfa.getSymbols();

        // Основной цикл
        Queue<Set<State>> unprocessedDFAStates = new LinkedList<>();
        unprocessedDFAStates.add(initialDFAState);
        while (!unprocessedDFAStates.isEmpty()) {
            Set<State> currentDFAState = unprocessedDFAStates.poll();
            for (Symbol symbol : symbols) {
                Set<State> nextState = new HashSet<>();
                for (State nfaState : currentDFAState) {
                    Set<State> transitionState = nfa.getTransitionFunction().transition(nfaState, symbol);
                    nextState.addAll(epsilonClosure(nfa, transitionState));
                }
                if (!dfaStates.contains(nextState)) {
                    unprocessedDFAStates.add(nextState);
                    dfaStates.add(nextState);
                }
                dfa.addTransition(currentDFAState, symbol, nextState);
            }
        }

        // Определяем множество заключительных состояний ДКА
        Set<Set<State>> dfaFinalStates = new HashSet<>();
        for (Set<State> dfaState : dfaStates) {
            for (State nfaState : dfaState) {
                if (nfa.getFinalStates().contains(nfaState)) {
                    dfaFinalStates.add(dfaState);
                    break;
                }
            }
        }
        dfa.setFinalStates(dfaFinalStates);

        return;
    }

    private static Set<State> epsilonClosure(NFA nfa, State state) {
        Set<State> closure = new HashSet<>();
        Stack<State> stack = new Stack<>();
        stack.push(state);

        while (!stack.isEmpty()) {
            State currentState = stack.pop();
            closure.add(currentState);

            Set<State> epsilonTransitions = currentState.getTransitions().get('\0'); // ε переход
            if (epsilonTransitions != null) {
                for (State epsilonState : epsilonTransitions) {
                    if (!closure.contains(epsilonState)) {
                        stack.push(epsilonState);
                    }
                }
            }
        }

        return closure;
    }

}
