package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.automaton.*;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertDFAToRegex2;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.*;
import java.util.HashSet;
import java.util.Set;

@Slf4j
public class TestConvertDFAToRegex2 {

    @Test
    public void testEpsilon() {
        State stateA = new State("A");
        State stateB = new State("B");

        Set<State> states = new HashSet<>();
        states.add(stateA);
        states.add(stateB);


        Symbol symbol0 = new Symbol("0");
        Symbol symbol1 = new Symbol("1");

        Set<Symbol> symbols = new HashSet<>();
        symbols.add(symbol0);
        symbols.add(symbol1);

        State initialState = stateA;

        Set<State> finalStates = new HashSet<>();
        finalStates.add(stateB);

        TransitionFunctionDFA transitionFunctionDFA = new TransitionFunctionDFA();
        transitionFunctionDFA.putToTable(stateA, symbol1, stateA);
        transitionFunctionDFA.putToTable(stateA, symbol0, stateB);
        transitionFunctionDFA.putToTable(stateB, symbol0, stateB);
        transitionFunctionDFA.putToTable(stateB, symbol1, stateB);

        DFA dfa = new DFA(states, symbols, initialState, finalStates, transitionFunctionDFA);

        ConvertDFAToRegex2 convertDFAToRegex2 = new ConvertDFAToRegex2(dfa);
        Regex convert = convertDFAToRegex2.convert();
        log.info(convert.toString());
    }
}
