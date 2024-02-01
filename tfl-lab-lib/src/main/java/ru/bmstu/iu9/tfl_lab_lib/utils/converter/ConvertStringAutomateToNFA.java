package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.TransitionFunctionNFA;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@UtilityClass
public class ConvertStringAutomateToNFA {
    public NFA convert(String automate) {
        List<String> split = List.of(automate.split("\n"));

        String startStateString = split.get(0);
        State initialState = new State(startStateString);

        List<String> finalStateStrings = getWordsStrings(split.get(1));
        Set<State> finalStates = new HashSet<>();
        for (String finalStateString : finalStateStrings) {
            State finalState = new State(finalStateString);
            finalStates.add(finalState);
        }

        Set<Symbol> symbols = new HashSet<>();
        Set<State> states = new HashSet<>();

        TransitionFunctionNFA transitionFunctionNFA = new TransitionFunctionNFA();
        List<String> transitionFunctionString = split.stream().skip(2).toList();
        for (String transition : transitionFunctionString) {
            List<String> wordsStrings = getWordsStrings(transition);
            State startState = new State(wordsStrings.get(0));
            Symbol symbol = new Symbol(wordsStrings.get(1));
            State nextState = new State(wordsStrings.get(2));
            transitionFunctionNFA.putToTable(startState, symbol, nextState);
            states.add(startState);
            states.add(nextState);
            symbols.add(symbol);
        }

        return new NFA(states, symbols, initialState, finalStates, transitionFunctionNFA);
    }

    private List<String> getWordsStrings(String input) {
        List<String> words = new ArrayList<>();
        Pattern pattern = Pattern.compile("\\b\\w+\\b");
        Matcher matcher = pattern.matcher(input);
        while (matcher.find()) {
            words.add(matcher.group());
        }
        return words;
    }
}
