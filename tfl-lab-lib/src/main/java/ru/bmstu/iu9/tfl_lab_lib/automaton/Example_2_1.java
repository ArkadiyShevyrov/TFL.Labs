package ru.bmstu.iu9.tfl_lab_lib.automaton;

import lombok.extern.slf4j.Slf4j;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.*;
import ru.bmstu.iu9.tfl_lab_lib.language.Language;
import java.util.*;

@Slf4j
public class Example_2_1 {
    public static void main(String[] args) {
        State state0 = new State();
        State state1 = new State();
        State state2 = new State();
        Symbol symbol0 = new Symbol();
        Symbol symbol1 = new Symbol();
        Set<State> states = new HashSet<>();
        states.add(state0);
        states.add(state1);
        states.add(state2);
        Set<Symbol> symbols = new HashSet<>();
        symbols.add(symbol0);
        symbols.add(symbol1);
        Set<State> finalStates = new HashSet<>();
        finalStates.add(state1);
        Map<State, Map<Symbol, State>> tableTransition = new HashMap<>();
        Map<Symbol, State> map0 = new HashMap<>();
        map0.put(symbol0, state2);
        map0.put(symbol1, state0);
        Map<Symbol, State> map1 = new HashMap<>();
        map1.put(symbol0, state1);
        map1.put(symbol1, state1);
        Map<Symbol, State> map2 = new HashMap<>();
        map2.put(symbol0, state2);
        map2.put(symbol1, state1);
        tableTransition.put(state0, map0);
        tableTransition.put(state1, map1);
        tableTransition.put(state2, map2);
        TransitionFunctionDFA transitionFunctionDFA = new TransitionFunctionDFA(tableTransition);
        DFA dfa = new DFA(states, symbols,state0, finalStates, transitionFunctionDFA);
        List<Symbol> string = new ArrayList<>();
        string.add(symbol1);
        string.add(symbol1);
        string.add(symbol1);
        string.add(symbol0);
        string.add(symbol1);
        StringSymbols stringSymbols = new StringSymbols(string);
        Language language = new Language(dfa);
        boolean validString1 = language.isValidString(stringSymbols);
        log.info(String.valueOf(validString1));
    }
}
