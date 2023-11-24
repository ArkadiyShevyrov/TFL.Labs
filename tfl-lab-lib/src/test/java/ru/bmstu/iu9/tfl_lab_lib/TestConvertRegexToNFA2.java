package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.automaton.ConvertRegexToNFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.NFA;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.Regex;
import static org.junit.jupiter.api.Assertions.assertEquals;

@Slf4j
public class TestConvertRegexToNFA2 {

    @Test
    public void testEpsilon() {
        Regex regex = new Regex(Regex.Type.EPSILON);
        NFA convert = ConvertRegexToNFA.convert(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(2, convert.getStates().size());
        assertEquals(1, convert.getSymbols().size());
    }

    @Test
    public void testEmpty() {
        Regex regex = new Regex(Regex.Type.EMPTY);
        NFA convert = ConvertRegexToNFA.convert(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(2, convert.getStates().size());
        assertEquals(0, convert.getSymbols().size());
    }

    @Test
    public void testSymbol() {
        Regex regex = new Regex(Regex.Type.SYMBOL, "a");
        NFA convert = ConvertRegexToNFA.convert(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(2, convert.getStates().size());
        assertEquals(1, convert.getSymbols().size());
    }


    @Test
    public void testOR() {
        Regex regex = new Regex(
                Regex.Type.OR,
                new Regex(Regex.Type.SYMBOL, "a"),
                new Regex(Regex.Type.SYMBOL, "b")
        );
        NFA convert = ConvertRegexToNFA.convert(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(6, convert.getStates().size());
        assertEquals(3, convert.getSymbols().size());
        assertEquals(5, convert.getTransitionFunction().getTableTransition().size());
    }

    @Test
    public void testConcat() {
        Regex regex = new Regex(
                Regex.Type.CONCAT,
                new Regex(Regex.Type.SYMBOL, "a"),
                new Regex(Regex.Type.SYMBOL, "b")
        );
        NFA convert = ConvertRegexToNFA.convert(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(4, convert.getStates().size());
        assertEquals(3, convert.getSymbols().size());
        assertEquals(3, convert.getTransitionFunction().getTableTransition().size());
    }

    @Test
    public void testAsterisk() {
        Regex regex = new Regex(
                Regex.Type.ASTERISK,
                new Regex(Regex.Type.SYMBOL, "a")
        );
        NFA convert = ConvertRegexToNFA.convert(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(4, convert.getStates().size());
        assertEquals(2, convert.getSymbols().size());
        assertEquals(3, convert.getTransitionFunction().getTableTransition().size());
    }
}
