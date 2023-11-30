package ru.bmstu.iu9.tfl_lab_lib.utils;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.DFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertDFAToRegex;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertDFAToRegex2;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertNFAToDFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertRegexToNFA;

@UtilityClass
public class Converter {
    public Regex convertDFAToRegex(DFA dfa) {
        return ConvertDFAToRegex.convert(dfa);
    }

    public Regex convertDFAToRegex2(DFA dfa) {
        return new ConvertDFAToRegex2(dfa).convert();
    }

    public NFA convertRegexToNFA(Regex regex) {
        return ConvertRegexToNFA.convert(regex);
    }

    public DFA convertNFAToDFA(NFA nfa) {
        return ConvertNFAToDFA.convert(nfa);
    }
}
