package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.DFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.TransitionFunctionDFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.optimize.OptimizeRegexForEpsilonAndEmpty;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ConvertDFAToRegex2 {
    private final TransitionFunctionDFA tf;
    private final List<State> states;
    private final State initialState;
    Set<State> finalStates;

    public ConvertDFAToRegex2(DFA dfa) {
        tf = dfa.getTransitionFunction();
        states = dfa.getStates().stream().toList();
        initialState = dfa.getInitialState();
        finalStates = dfa.getFinalStates();
    }

    public Regex convert() {
        List<Regex> list = new ArrayList<>();
        for (State finalState : finalStates) {
            list.add(getRegex(initialState, finalState, states.size() - 1));
        }
        return combinateRegex(list);
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

    private Regex getRegex(State stateI, State stateJ, int numberK) {
        if (numberK == -1) {
            List<Regex> listRegex = new ArrayList<>();
            if (stateI.equals(stateJ)) {
                listRegex.add(new Regex(Regex.Type.EPSILON));
                Map<Symbol, State> symbolStateMap = tf.getTableTransition().get(stateI);
                for (Symbol symbol : symbolStateMap.keySet()) {
                    State state = symbolStateMap.get(symbol);
                    if (state.equals(stateJ)) {
                        listRegex.add(new Regex(symbol.getString()));
                    }
                }
            } else {
                Map<Symbol, State> symbolStateMap = tf.getTableTransition().get(stateI);
                for (Symbol symbol : symbolStateMap.keySet()) {
                    State state = symbolStateMap.get(symbol);
                    if (state.equals(stateJ)) {
                        listRegex.add(new Regex(symbol.getString()));
                    }
                }
            }
            return OptimizeRegexForEpsilonAndEmpty.optimize(combinateRegex(listRegex));
        } else {
            State stateK = states.get(numberK);
            int numberK1 = numberK - 1;
            return OptimizeRegexForEpsilonAndEmpty.optimize(new Regex(
                    Regex.Type.OR,
                    getRegex(stateI, stateJ, numberK1),
                    new Regex(
                            Regex.Type.CONCAT,
                            getRegex(stateI, stateK, numberK1),
                            new Regex(
                                    Regex.Type.CONCAT,
                                    new Regex(
                                            Regex.Type.ASTERISK,
                                            getRegex(stateK, stateK, numberK1)
                                    ),
                                    getRegex(stateK, stateJ, numberK1)
                            )
                    )
            ));
        }
    }
}
