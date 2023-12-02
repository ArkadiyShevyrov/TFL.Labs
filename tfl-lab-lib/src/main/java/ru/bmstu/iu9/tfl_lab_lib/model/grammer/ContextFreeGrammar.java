package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.Set;

@Getter
@AllArgsConstructor
public class ContextFreeGrammar {
    private Set<Variable> variables;
    private Set<Terminal> terminals;
    private Productions productions;
    private Variable startVariable;
}
