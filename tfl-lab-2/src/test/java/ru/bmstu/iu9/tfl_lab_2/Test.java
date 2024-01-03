package ru.bmstu.iu9.tfl_lab_2;

import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.DFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertNFAToDFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertRegexToNFA;
import java.util.Random;

public class Test {
    public static void main(String[] args) {
        Regex regex = RandomRegexGenerator.generateRandomRegex(5, 2, 5);
        ConvertRegexToNFA convertRegexToNFA = new ConvertRegexToNFA();
        NFA nfa = convertRegexToNFA.convert(regex);
        DFA dfa = ConvertNFAToDFA.convert(nfa);
        System.out.println();
    }
}
