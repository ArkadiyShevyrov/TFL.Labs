package ru.bmstu.iu9.tfl_lab_lib.utils.generator;

import ru.bmstu.iu9.tfl_lab_lib.model.grammer.*;
import java.util.ArrayList;
import java.util.List;

public class GenerateParsingTree {
    private final Productions productions;
    private final Variable startVariable;
    public GenerateParsingTree(CFGrammar cfGrammar) {
        this.productions = cfGrammar.getProductions();
        this.startVariable = cfGrammar.getStartVariable();
    }

    public ParsingTree generate(TerminalString terminalString) {
        return deriveStringsLeft(startVariable, terminalString);
    }

    private ParsingTree deriveStringsLeft(Variable variableStart, TerminalString terminalString) {
        if (productions.getTableProductions().containsKey(variableStart)) {
            for (GrammarString grammarString : productions.getTableProductions().get(variableStart)) {
                int currentIndex = 0;
                boolean validGrammarString = true;
                List<ParsingTree> children = new ArrayList<>();
                for (GrammarUnit grammarUnit : grammarString.getGrammarUnits()) {
                    ParsingTree child = null;
                    if (grammarUnit instanceof Terminal terminal) {
                        if (terminal.getType() == Terminal.Type.EPSILON) {
                            child = new ParsingTree(terminal);
                        } else {
                            if (terminalString.length() == 0) {
                                validGrammarString = false;
                                break;
                            }
                            Terminal first = terminalString.get(currentIndex);
                            if (terminal.equals(first)) {
                                child = new ParsingTree(terminal);
                            } else {
                                validGrammarString = false;
                                break;
                            }
                        }
                    } else if (grammarUnit instanceof Variable variable) {
                        child = deriveStringsLeft(variable, terminalString.substring(currentIndex));
                        if (child == null) {
                            validGrammarString = false;
                            break;
                        }
                    }
                    assert child != null;
                    currentIndex += child.length();
                    children.add(child);
                }
                if (validGrammarString) {
                    return new ParsingTree(variableStart, children);
                }
            }
        }
        return null;
    }
}
