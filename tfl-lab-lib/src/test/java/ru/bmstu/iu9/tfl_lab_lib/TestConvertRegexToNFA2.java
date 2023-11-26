package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.automaton.ConvertDFAToRegex;
import ru.bmstu.iu9.tfl_lab_lib.automaton.ConvertNFAToDFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.ConvertRegexToNFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.*;
import ru.bmstu.iu9.tfl_lab_lib.language.Language;
import java.util.ArrayList;
import java.util.List;

@Slf4j
public class TestConvertRegexToNFA2 {

    @Test
    public void testEpsilon() {

        Regex regex = new Regex(
                Regex.Type.CONCAT,
                new Regex(
                        Regex.Type.ASTERISK,
                        new Regex(
                                Regex.Type.OR,
                                new Regex("0"),
                                new Regex("1")
                        )
                ),
                new Regex(
                        Regex.Type.CONCAT,
                        new Regex("1"),
                        new Regex(
                                Regex.Type.OR,
                                new Regex("0"),
                                new Regex("1")
                        )
                )
        );
        NFA nfa = ConvertRegexToNFA.convert(regex);
        DFA dfa = ConvertNFAToDFA.convert(nfa);
        Language language = new Language(dfa);
        List<Symbol> s = new ArrayList<>();
        s.add(new Symbol("0"));
        s.add(new Symbol("1"));
        StringSymbols symbols = new StringSymbols(s);
        boolean validString = language.isValidString(symbols);
        Regex convert = ConvertDFAToRegex.convert(dfa);
        NFA nfa2 = ConvertRegexToNFA.convert(convert);
        DFA dfa2 = ConvertNFAToDFA.convert(nfa);
        Language language2 = new Language(dfa2);
        boolean validString2 = language2.isValidString(symbols);
        log.info(convert.toString());
    }
}
