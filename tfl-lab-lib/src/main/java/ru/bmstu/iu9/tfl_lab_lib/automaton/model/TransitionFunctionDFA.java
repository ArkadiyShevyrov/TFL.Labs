package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

@Getter
@AllArgsConstructor
public class TransitionFunctionDFA implements TransitionFunction, Serializable {

    private Map<State, Map<Symbol, State>> tableTransition;

    public TransitionFunctionDFA() {
        this.tableTransition = new HashMap<>();
    }

    @Override
    public State transition(State state, Symbol symbol) {
        return tableTransition.get(state).get(symbol);
    }

    public State advancedTransition(State state, StringSymbols symbols) {
        return transition(advancedTransition(state, symbols.getAllExpectLast()), symbols.getLast());
    }


    public void putToTable(State stateStart, Symbol symbol, State stateEnd) {
        Map<Symbol, State> oldMap = tableTransition.get(stateStart);
        Map<Symbol, State> newMap = Objects.requireNonNullElseGet(oldMap, HashMap::new);
        newMap.put(symbol, stateEnd);
        tableTransition.put(stateStart, newMap);
    }

    public void putToTable(State stateStart) {
        tableTransition.put(stateStart, new HashMap<>());
    }


    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();

        for (Map.Entry<State, Map<Symbol, State>> entry : tableTransition.entrySet()) {
            State key = entry.getKey();
            Map<Symbol, State> value = entry.getValue();

            for (Map.Entry<Symbol, State> innerEntry : value.entrySet()) {
                Symbol innerKey = innerEntry.getKey();
                State innerValue = innerEntry.getValue();

                stringBuilder.append(key).append(" -> ").append(innerKey).append(" -> ").append(innerValue).append("\n");
            }
        }
        return "\n" +stringBuilder.toString().trim();
    }
}
