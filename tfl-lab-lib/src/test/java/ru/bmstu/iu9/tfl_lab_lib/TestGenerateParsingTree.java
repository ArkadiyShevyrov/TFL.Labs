package ru.bmstu.iu9.tfl_lab_lib;

import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.model.grammer.*;
import ru.bmstu.iu9.tfl_lab_lib.utils.generator.GenerateParsingTree;
import java.util.HashSet;
import java.util.Set;

@Slf4j
public class TestGenerateParsingTree {
    @Test
    public void testConcat() {
        TerminalString terminalString = new TerminalString("00101");

        Variable variableS = new Variable("S");
        Variable variableA = new Variable("A");
        Variable variableB = new Variable("B");

        Set<Variable> variables = new HashSet<>();
        variables.add(variableS);
        variables.add(variableA);
        variables.add(variableB);

        Terminal terminal0 = new Terminal("0");
        Terminal terminal1 = new Terminal("1");
        Terminal terminalEpsilon = new Terminal(Terminal.Type.EPSILON);

        Set<Terminal> terminals = new HashSet<>();
        terminals.add(terminal0);
        terminals.add(terminal1);
        terminals.add(terminalEpsilon);

        Productions productions = new Productions();
        productions.putToTable(variableS,
                new GrammarString(variableA, terminal1, variableB));
        productions.putToTable(variableA,
                new GrammarString(terminal0, variableA),
                new GrammarString(terminalEpsilon));
        productions.putToTable(variableB,
                new GrammarString(terminal0, variableB),
                new GrammarString(terminal1, variableB),
                new GrammarString(terminalEpsilon));


        Variable startVariable = variableS;

        CFGrammar cfGrammar = new CFGrammar(variables, terminals, productions, startVariable);
        GenerateParsingTree generateParsingTree = new GenerateParsingTree(cfGrammar);
        ParsingTree generate = generateParsingTree.generate(terminalString);
        String s = generate.drawTree(generate);
        log.info(s);
    }
}
