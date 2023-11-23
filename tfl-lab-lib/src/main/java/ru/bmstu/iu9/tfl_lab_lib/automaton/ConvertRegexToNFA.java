package ru.bmstu.iu9.tfl_lab_lib.automaton;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

@UtilityClass
public class ConvertRegexToNFA {
    public static int currentNumber = 0;

    //    Theorem 3.7. Any language defined by a regular expression can be defined by some finite automaton;
    public NFA convert(Regex regex) {
        switch (regex.getType()) {
            // Basis
            case EPSILON -> {
                return getEpsilonFA();
            }
            default -> {
                return getEmptyFA();
            }
            case SYMBOL -> {
                return getSymbolFA(new Symbol(regex.getValue()));
            }
            // Induction
            case OR -> {
                return getOrFA(convert(regex.getLeft()), convert(regex.getRight()));
            }
            case CONCAT -> {
                return getConcatFA(convert(regex.getLeft()), convert(regex.getRight()));
            }
            case ASTERISK -> {
                return getAsteriskFA(convert(regex.getLeft()));
            }
        }
    }

    private NFA getEpsilonFA() {
        State initialState = new State(String.valueOf(currentNumber++));
        State finalState = new State(String.valueOf(currentNumber++));

        Set<State> states = new HashSet<>();
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>();
        symbols.add(new Symbol(Symbol.Type.EPSILON));

        Set<State> finalStates = new HashSet<>();
        finalStates.add(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putToTable(initialState, new Symbol(Symbol.Type.EPSILON), finalStates);

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getEmptyFA() {
        State initialState = new State(String.valueOf(currentNumber++));
        State finalState = new State(String.valueOf(currentNumber++));

        Set<State> states = new HashSet<>();
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>();

        Set<State> finalStates = new HashSet<>();
        finalStates.add(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getSymbolFA(Symbol symbol) {
        State initialState = new State(String.valueOf(currentNumber++));
        State finalState = new State(String.valueOf(currentNumber++));

        Set<State> states = new HashSet<>();
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>();
        symbols.add(symbol);

        Set<State> finalStates = new HashSet<>();
        finalStates.add(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putToTable(initialState, symbol, finalStates);

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getOrFA(NFA leftNFA, NFA rightNFA) {
//        State initialState = new State(String.valueOf(currentNumber++));
//        State finalState = new State(String.valueOf(currentNumber++));
//        Set<State> states = new HashSet<>();
//        states.add(initialState);
//        states.add(finalState);
//        Set<Symbol> symbols = new HashSet<>();
//        symbols.add(symbol);
//        Set<State> finalStates = new HashSet<>();
//        finalStates.add(finalState);
//        Map<State, Map<Symbol, Set<State>>> tableTransition = new HashMap<>();
//        putTable(tableTransition, initialState, symbol, finalStates);
//        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA(tableTransition);
//        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getConcatFA(NFA leftNFA, NFA rightNFA) {
        State initialState = leftNFA.getInitialState();

        Set<State> finalStates = rightNFA.getFinalStates();

        Set<State> states = new HashSet<>();
        states.addAll(leftNFA.getStates());
        states.addAll(rightNFA.getStates());

        Set<Symbol> symbols = new HashSet<>();
        symbols.addAll(leftNFA.getSymbols());
        symbols.addAll(rightNFA.getSymbols());
        symbols.add(new Symbol(Symbol.Type.EPSILON));

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putAll(leftNFA.getTransitionFunction());
        transitionFunction.putAll(rightNFA.getTransitionFunction());
        Set<State> finalStatesLeft = leftNFA.getFinalStates();
        State finalStateLeft = new State();
        for (State state : finalStatesLeft) {
            finalStateLeft = state;
        }
        State initialStatRight = rightNFA.getInitialState();
        Set<State> initialStatesRight = new HashSet<>();
        initialStatesRight.add(initialStatRight);
        transitionFunction.putToTable(finalStateLeft, new Symbol(Symbol.Type.EPSILON), initialStatesRight);

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getAsteriskFA(NFA leftNFA) {
//        State initialState = new State(String.valueOf(currentNumber++));
//        State finalState = new State(String.valueOf(currentNumber++));
//        Set<State> states = new HashSet<>();
//        states.add(initialState);
//        states.add(finalState);
//        Set<Symbol> symbols = new HashSet<>();
//        symbols.add(symbol);
//        Set<State> finalStates = new HashSet<>();
//        finalStates.add(finalState);
//        Map<State, Map<Symbol, Set<State>>> tableTransition = new HashMap<>();
//        putTable(tableTransition, initialState, symbol, finalStates);
//        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA(tableTransition);
//        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }


}
