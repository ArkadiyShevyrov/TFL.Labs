package ru.bmstu.iu9.tfl_lab_lib.utils.grammar;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.grammer.*;
import java.util.*;

@UtilityClass
public class GrammarFollow {
    public Map<Variable, Set<Terminal>> constructFollow(CFGrammar grammar) {
        Map<Variable, Set<Terminal>> follows = new HashMap<>();
        for (Variable variable : grammar.getVariables()) {
            follows.put(variable, new HashSet<>());
        }
        follows.put(grammar.getStartVariable(), new HashSet<>(List.of(Terminal.endString)));
        boolean changed = true;
        while (changed) {
            changed = false;
            HashMap<Variable, List<GrammarString>> tableProductions = grammar.getProductions().getTableProductions();
            for (Variable variableA : tableProductions.keySet()) {
                List<GrammarString> grammarStrings = tableProductions.get(variableA);
                for (GrammarString grammarString : grammarStrings) {
                    for (int i = 0; i < grammarString.size(); i++) {
                        GrammarUnit grammarUnit = grammarString.get(i);
                        if (grammarUnit instanceof Variable variableB) {
                            GrammarString substringNext = grammarString.substring(i+1);
                            Set<Terminal> first = first(substringNext, grammar);
                            Set<Terminal> firstNotEpsilon = new HashSet<>(first);
                            firstNotEpsilon.remove(Terminal.epsilon);
                            Set<Terminal> terminalsB = follows.get(variableB);
                            if (terminalsB.addAll(firstNotEpsilon)) {
                                changed = true;
                            }
                            if (first.contains(Terminal.epsilon)) {
                                Set<Terminal> terminalsA = follows.get(variableA);
                                if (terminalsB.addAll(terminalsA)) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return follows;
    }

    public Map<Variable, Set<Terminal>> constructFirst(CFGrammar grammar) {
        Map<Variable, Set<Terminal>> firsts = new HashMap<>();
        for (Variable variable : grammar.getVariables()) {
            firsts.put(variable, new HashSet<>());
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            HashMap<Variable, List<GrammarString>> tableProductions = grammar.getProductions().getTableProductions();
            Set<Variable> variables = tableProductions.keySet();
            for (Variable variable : variables) {
                List<GrammarString> grammarStrings = tableProductions.get(variable);
                for (GrammarString grammarString : grammarStrings) {
                    Set<Terminal> terminals = firsts.get(variable);
                    if (terminals.addAll(first(grammarString, grammar))) {
                        changed = true;
                    }
                }
            }
        }
        return firsts;
    }

    public Set<Terminal> first(GrammarString grammarString, CFGrammar grammar) {
        return first(grammarString, grammar, new HashSet<>());
    }


    public Set<Terminal> first(GrammarString grammarString, CFGrammar grammar, Set<Variable> visited) {
        if (grammarString.size() == 0) {
            return new HashSet<>(List.of(Terminal.epsilon));
        }
        Set<Terminal> first = new HashSet<>();
        for (GrammarUnit grammarUnit : grammarString.getGrammarUnits()) {
            if (grammarUnit instanceof Terminal terminal) {
                first.add(terminal);
                break;
            } else if (grammarUnit instanceof Variable variable) {
                List<GrammarString> grammarStrings = grammar.getProductions().getTableProductions().get(variable);
                // Проверяем, посещали ли мы этот нетерминал ранее
                if (!visited.contains(variable)) {
                    visited.add(variable);
                    List<GrammarString> productions = grammar.getProductions().getTableProductions().get(variable);
                    for (GrammarString production : productions) {
                        Set<Terminal> firstOfProduction = first(production, grammar, visited);
                        first.addAll(firstOfProduction);
                        if (!firstOfProduction.contains(Terminal.epsilon)) {
                            break;
                        }
                    }
                    visited.remove(variable);
                }
            }
        }
        return first;
    }
}
