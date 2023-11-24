package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.automaton.ConvertDFAToRegex;
import ru.bmstu.iu9.tfl_lab_lib.automaton.ConvertRegexToNFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.*;
import java.util.HashSet;
import java.util.Set;
import static org.junit.jupiter.api.Assertions.assertEquals;

@Slf4j
public class TestConvertDFAToRegex {

    @Test
    public void testEpsilon() {
        State stateA = new State("A");
        State stateB = new State("B");
        State stateC = new State("C");
        State stateD = new State("D");

        Set<State> states = new HashSet<>();
        states.add(stateA);
        states.add(stateB);
        states.add(stateC);
        states.add(stateD);

        Symbol symbol0 = new Symbol("0");
        Symbol symbol1 = new Symbol("1");

        Set<Symbol> symbols = new HashSet<>();
        symbols.add(symbol0);
        symbols.add(symbol1);

        State initialState = stateA;

        Set<State> finalStates = new HashSet<>();
        finalStates.add(stateC);
        finalStates.add(stateD);

        TransitionFunctionDFA transitionFunctionDFA = new TransitionFunctionDFA();
        transitionFunctionDFA.putToTable(stateA , symbol0, stateA);
        transitionFunctionDFA.putToTable(stateA , symbol1, stateB);
        transitionFunctionDFA.putToTable(stateB , symbol0, stateC);
        transitionFunctionDFA.putToTable(stateB , symbol1, stateC);
        transitionFunctionDFA.putToTable(stateC , symbol0, stateD);
        transitionFunctionDFA.putToTable(stateC , symbol1, stateD);
        transitionFunctionDFA.putToTable(stateD);

        DFA dfa = new DFA(states, symbols, initialState, finalStates, transitionFunctionDFA);
        Regex convert = OptimizeRegex.optimize(ConvertDFAToRegex.convert(dfa));
        log.info(convert.toString());
    }
}
