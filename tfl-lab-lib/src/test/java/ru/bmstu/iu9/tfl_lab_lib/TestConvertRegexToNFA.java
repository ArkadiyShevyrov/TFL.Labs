package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.Converter;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertRegexToNFA;
import static org.junit.jupiter.api.Assertions.assertEquals;

@Slf4j
public class TestConvertRegexToNFA {

    @Test
    public void testEpsilon() {
        Regex regex = new Regex(Regex.Type.EPSILON);
        NFA convert = Converter.convertRegexToNFA(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(2, convert.getStates().size());
        assertEquals(1, convert.getSymbols().size());
    }

    @Test
    public void testEmpty() {
        Regex regex = new Regex(Regex.Type.EMPTY);
        NFA convert = Converter.convertRegexToNFA(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(2, convert.getStates().size());
        assertEquals(0, convert.getSymbols().size());
    }

    @Test
    public void testSymbol() {
        Regex regex = new Regex(Regex.Type.SYMBOL, "a");
        NFA convert = Converter.convertRegexToNFA(regex);
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
        NFA convert = Converter.convertRegexToNFA(regex);
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
        NFA convert = Converter.convertRegexToNFA(regex);
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
        NFA convert = Converter.convertRegexToNFA(regex);
        log.info(convert.getTransitionFunction().toString());
        assertEquals(4, convert.getStates().size());
        assertEquals(2, convert.getSymbols().size());
        assertEquals(3, convert.getTransitionFunction().getTableTransition().size());
    }
}
