package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.model.Language;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.DFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.StringSymbols;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertDFAToRegex;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertNFAToDFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertRegexToNFA;

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
        StringSymbols symbols = new StringSymbols("01");
        boolean validString = language.isValidString(symbols);
        Regex convert = ConvertDFAToRegex.convert(dfa);
        NFA nfa2 = ConvertRegexToNFA.convert(convert);
        DFA dfa2 = ConvertNFAToDFA.convert(nfa);
        Language language2 = new Language(dfa2);
        boolean validString2 = language2.isValidString(symbols);
        log.info(convert.toString());
    }
}
