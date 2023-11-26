package ru.bmstu.iu9.tfl_lab_lib.automaton;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.*;
import java.util.HashSet;
import java.util.Set;

@UtilityClass
public class ConvertRegexToNFA {
    private static final Symbol epsilon = new Symbol(Symbol.Type.EPSILON);
    private static int currentNumber = 0;

    //    Theorem 3.7. Any language defined by a regular expression can be defined by some finite automaton;
    public NFA convert(Regex regex) {
        return switch (regex.getType()) {
            case EPSILON -> getEpsilonFA();
            case EMPTY -> getEmptyFA();
            case SYMBOL -> getSymbolFA(new Symbol(regex.getValue()));
            case OR -> getOrFA(convert(regex.getLeft()), convert(regex.getRight()));
            case CONCAT -> getConcatFA(convert(regex.getLeft()), convert(regex.getRight()));
            case ASTERISK -> getAsteriskFA(convert(regex.getLeft()));
        };
    }


    private NFA getEpsilonFA() {
        State initialState = getInitialState();
        State finalState = getInitialState();

        Set<State> states = new HashSet<>();
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>();
        symbols.add(epsilon);

        Set<State> finalStates = trans(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putToTable(initialState, epsilon, finalStates);

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getEmptyFA() {
        State initialState = getInitialState();
        State finalState = getInitialState();

        Set<State> states = new HashSet<>();
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>();

        Set<State> finalStates = trans(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getSymbolFA(Symbol symbol) {
        State initialState = getInitialState();
        State finalState = getInitialState();

        Set<State> states = new HashSet<>();
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>();
        symbols.add(symbol);

        Set<State> finalStates = trans(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putToTable(initialState, symbol, finalStates);

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getOrFA(NFA leftNFA, NFA rightNFA) {
        State initialState = getInitialState();
        State finalState = getInitialState();

        Set<State> states = new HashSet<>();
        states.addAll(leftNFA.getStates());
        states.addAll(rightNFA.getStates());
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>();
        symbols.addAll(leftNFA.getSymbols());
        symbols.addAll(rightNFA.getSymbols());
        symbols.add(epsilon);

        Set<State> finalStates = trans(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putAll(leftNFA.getTransitionFunction());
        transitionFunction.putAll(rightNFA.getTransitionFunction());
        transitionFunction.putToTable(initialState, epsilon, trans(leftNFA.getInitialState()));
        transitionFunction.putToTable(initialState, epsilon, trans(rightNFA.getInitialState()));
        transitionFunction.putToTable(trans(leftNFA.getFinalStates()), epsilon, finalStates);
        transitionFunction.putToTable(trans(rightNFA.getFinalStates()), epsilon, finalStates);

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
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
        symbols.add(epsilon);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putAll(leftNFA.getTransitionFunction());
        transitionFunction.putAll(rightNFA.getTransitionFunction());
        transitionFunction.putToTable(trans(leftNFA.getFinalStates()), epsilon, trans(rightNFA.getInitialState()));

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }

    private NFA getAsteriskFA(NFA leftNFA) {
        State initialState = getInitialState();
        State finalState = getInitialState();

        Set<State> states = new HashSet<>(leftNFA.getStates());
        states.add(initialState);
        states.add(finalState);

        Set<Symbol> symbols = new HashSet<>(leftNFA.getSymbols());
        symbols.add(epsilon);

        Set<State> finalStates = trans(finalState);

        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();
        transitionFunction.putAll(leftNFA.getTransitionFunction());
        transitionFunction.putToTable(initialState, epsilon, trans(leftNFA.getInitialState()));
        transitionFunction.putToTable(trans(leftNFA.getFinalStates()), epsilon, trans(leftNFA.getInitialState()));
        transitionFunction.putToTable(trans(leftNFA.getFinalStates()), epsilon, trans(finalState));
        transitionFunction.putToTable(initialState, epsilon, finalStates);

        return new NFA(states, symbols, initialState, finalStates, transitionFunction);
    }


    private State trans(Set<State> states) {
        State res = new State();
        for (State state : states) {
            res = state;
        }
        return res;
    }

    private Set<State> trans(State state) {
        Set<State> res = new HashSet<>();
        res.add(state);
        return res;
    }

    private State getInitialState() {
        return new State(String.valueOf(currentNumber++));
    }

}
