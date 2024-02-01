package ru.bmstu.iu9.tfl_lab_lib;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.grammer.*;
import java.util.HashSet;
import java.util.Set;

@UtilityClass
public class StandardGrammar {

    public CFGrammar standardGrammarRegex() {
        Variable variableRegex = new Variable("regex");
        Variable variableTerm = new Variable("term");
        Variable variableFactor = new Variable("factor");
        Variable variableSymbol = new Variable("symbol");
        Variable variableChar = new Variable("char");

        Set<Variable> variables = new HashSet<>();
        variables.add(variableRegex);
        variables.add(variableTerm);
        variables.add(variableFactor);
        variables.add(variableSymbol);
        variables.add(variableChar);

        Terminal terminalA = new Terminal("a");
        Terminal terminalB = new Terminal("b");
        Terminal terminalC = new Terminal("c");
        Terminal terminalOr = new Terminal("|");
        Terminal terminalAsterisk = new Terminal("*");
        Terminal terminalOpen = new Terminal("(");
        Terminal terminalClose = new Terminal(")");

        Set<Terminal> terminals = new HashSet<>();
        terminals.add(terminalA);
        terminals.add(terminalB);
        terminals.add(terminalC);

        Productions productions = new Productions();
        productions.putToTable(variableRegex,
                new GrammarString(variableTerm),
                new GrammarString(variableTerm, terminalOr, variableRegex));
        productions.putToTable(variableTerm,
                new GrammarString(variableFactor),
                new GrammarString(variableFactor, variableTerm));
        productions.putToTable(variableFactor,
                new GrammarString(variableSymbol),
                new GrammarString(variableSymbol, terminalAsterisk));
        productions.putToTable(variableSymbol,
                new GrammarString(variableChar),
                new GrammarString(terminalOpen, variableRegex, terminalClose));
        productions.putToTable(variableChar,
                new GrammarString(terminalA),
                new GrammarString(terminalB),
                new GrammarString(terminalC));

        return new CFGrammar(variables, terminals, productions, variableRegex);
    }
}
