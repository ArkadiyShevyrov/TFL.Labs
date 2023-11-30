package ru.bmstu.iu9.tfl_lab_lib.utils;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertDFAToRegex2;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertRegexToNFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.DFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.Regex;

@UtilityClass
public class Converter {

    public Regex convertDFAToRegex2(DFA dfa) {
        return new ConvertDFAToRegex2(dfa).convert();
    }

    public NFA convertRegexToNFA(Regex regex) {
        return ConvertRegexToNFA.convert(regex);
    }
}
