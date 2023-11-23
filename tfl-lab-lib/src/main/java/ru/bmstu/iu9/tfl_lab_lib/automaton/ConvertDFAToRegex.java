package ru.bmstu.iu9.tfl_lab_lib.automaton;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.DFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.State;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

@UtilityClass
public class ConvertDFAToRegex {

    public Regex convert(DFA dfa) {
        List<Regex> regexes = new ArrayList<>();
        Set<State> finalStates = dfa.getFinalStates();
        for (State finalState : finalStates) {
            Regex regex = exclusion(dfa, finalState);
            regexes.add(regex);
        }
        return combinateRegex(regexes);
    }

    private Regex combinateRegex(List<Regex> regexes) {
        if (regexes.size() == 0) {
            return null;
        }
        if (regexes.size() == 1) {
            return regexes.get(0);
        }
        Regex res = new Regex(Regex.Type.OR, regexes.get(0));
        Regex current = res;
        for (int i = 1; i < regexes.size(); i++) {
            Regex regex = regexes.get(i);
            if (i == regexes.size() -1) {
                current.setRight(regex);
                break;
            }
            Regex right = new Regex(Regex.Type.OR, regex);
            current.setRight(right);
            current = right;
        }
        return res;
    }

    private Regex exclusion(DFA dfa, State finalState) {
        return null;
    }
}
