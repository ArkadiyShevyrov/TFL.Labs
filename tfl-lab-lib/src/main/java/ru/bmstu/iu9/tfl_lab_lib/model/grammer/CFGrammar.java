package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.Set;

@Getter
@AllArgsConstructor
// ContextFreeGrammar
public class CFGrammar {
    private Set<Variable> variables;
    private Set<Terminal> terminals;
    private Productions productions;
    private Variable startVariable;
}
