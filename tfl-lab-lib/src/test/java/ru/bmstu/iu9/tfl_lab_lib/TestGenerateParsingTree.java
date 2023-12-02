package ru.bmstu.iu9.tfl_lab_lib;

import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_lib.model.grammer.*;
import ru.bmstu.iu9.tfl_lab_lib.utils.generator.GenerateParsingTree;
import java.util.HashSet;
import java.util.Set;

public class TestGenerateParsingTree {
    @Test
    public void testConcat() {
        TerminalString terminalString = new TerminalString("a*(a+b00)");

        Variable variableE = new Variable("E");
        Variable variableI = new Variable("I");

        Set<Variable> variables = new HashSet<>();
        variables.add(variableE);
        variables.add(variableI);

        Terminal terminalA = new Terminal("a");
        Terminal terminalB = new Terminal("b");
        Terminal terminal0 = new Terminal("0");
        Terminal terminal1 = new Terminal("1");
        Terminal terminalPlus = new Terminal("+");
        Terminal terminalAsterisk = new Terminal("*");
        Terminal terminalLeft = new Terminal("(");
        Terminal terminalRight = new Terminal(")");

        Set<Terminal> terminals = new HashSet<>();
        terminals.add(terminalA);
        terminals.add(terminalB);
        terminals.add(terminal0);
        terminals.add(terminal1);
        terminals.add(terminalPlus);
        terminals.add(terminalAsterisk);
        terminals.add(terminalLeft);
        terminals.add(terminalRight);

        Productions productions = new Productions();
        productions.putToTable(variableE, new GrammarString(variableI));
        productions.putToTable(variableE, new GrammarString(variableE, terminalPlus, variableE));
        productions.putToTable(variableE, new GrammarString(variableE, terminalAsterisk, variableE));
        productions.putToTable(variableE, new GrammarString(terminalLeft, variableE, terminalRight));
        productions.putToTable(variableI, new GrammarString(terminalA));
        productions.putToTable(variableI, new GrammarString(terminalB));
        productions.putToTable(variableI, new GrammarString(variableI, terminalA));
        productions.putToTable(variableI, new GrammarString(variableI, terminalB));
        productions.putToTable(variableI, new GrammarString(variableI, terminal0));
        productions.putToTable(variableI, new GrammarString(variableI, terminal1));


        Variable startVariable = variableE;

        CFGrammar cfGrammar = new CFGrammar(variables, terminals, productions, startVariable);
        GenerateParsingTree generateParsingTree = new GenerateParsingTree(cfGrammar);
        ParsingTree generate = generateParsingTree.generate(terminalString);
        System.out.println();
    }
}
