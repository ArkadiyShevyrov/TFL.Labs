package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.automaton.model.Regex;
import java.util.ArrayList;
import java.util.List;

@Slf4j
public class TestTst {

    @Test
    public void testEpsilon() {

        Regex a2 = new Regex(Regex.Type.EPSILON);
        Regex a3 = new Regex(Regex.Type.SYMBOL, "b");
        Regex a31 = new Regex(Regex.Type.SYMBOL, "a");
        Regex a32 = new Regex(Regex.Type.SYMBOL, "c");
        Regex a1 = new Regex(Regex.Type.EMPTY);
        Regex a4 = new Regex(Regex.Type.OR, a1, a2);
        Regex a5 = new Regex(Regex.Type.CONCAT, a1, a2);
        Regex a6 = new Regex(Regex.Type.ASTERISK, a1);
        List<Regex> regexes = new ArrayList<>();
        regexes.add(a6);

        regexes.add(a4);
        regexes.add(a3);
        regexes.add(a2);
        regexes.add(a1);
        regexes.add(a31);
        regexes.add(a5);
        regexes.add(a32);
        List<Regex> regexes1 = regexes.stream().sorted().toList();
        System.out.println();
    }
}
