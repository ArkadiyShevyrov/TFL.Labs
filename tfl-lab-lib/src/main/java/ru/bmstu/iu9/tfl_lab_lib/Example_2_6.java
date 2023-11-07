package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import ru.bmstu.iu9.tfl_lab_lib.model.*;
import java.util.*;

@Slf4j
public class Example_2_6 {
    public static void main(String[] args) {
        State state0 = new State("q0");
        State state1 = new State("q1");
        State state2 = new State("q2");
        Symbol symbol0 = new Symbol("0", Symbol.Type.SYMBOL);
        Symbol symbol1 = new Symbol("1", Symbol.Type.SYMBOL);
        Set<State> states = new HashSet<>();
        states.add(state0);
        states.add(state1);
        states.add(state2);
        Set<Symbol> symbols = new HashSet<>();
        symbols.add(symbol0);
        symbols.add(symbol1);
        Set<State> finalStates = new HashSet<>();
        finalStates.add(state2);
        Map<State, Map<Symbol, Set<State>>> tableTransition = new HashMap<>();
        Map<Symbol, Set<State>> map0 = new HashMap<>();
        Set<State> s00 = new HashSet<>();
        s00.add(state0);
        s00.add(state1);
        Set<State> s01 = new HashSet<>();
        s01.add(state0);
        map0.put(symbol0, s00);
        map0.put(symbol1, s01);
        Map<Symbol, Set<State>> map1 = new HashMap<>();
        map1.put(symbol0, new HashSet<>());
        Set<State> s11 = new HashSet<>();
        s11.add(state2);
        map1.put(symbol1, s11);
        Map<Symbol, Set<State>> map2 = new HashMap<>();
        map2.put(symbol0, new HashSet<>());
        map2.put(symbol1, new HashSet<>());
        tableTransition.put(state0, map0);
        tableTransition.put(state1, map1);
        tableTransition.put(state2, map2);
        TransitionFunctionNFA transitionFunctionNFA = new TransitionFunctionNFA(tableTransition);
        NFA nfa = new NFA(states, symbols,state0, finalStates, transitionFunctionNFA);

        DFA convert = ConvertNFAToDFA.convert(nfa);
        System.out.println();
    }
}
