package ru.bmstu.iu9.tfl_lab_lib.model.automaton;

import lombok.AllArgsConstructor;
import lombok.Getter;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

@Getter
@AllArgsConstructor
public class TransitionFunctionNFA implements TransitionFunction {

    private Map<State, Map<Symbol, Set<State>>> tableTransition;

    private Symbol epsilon = new Symbol(Symbol.Type.EPSILON);

    public TransitionFunctionNFA(Map<State, Map<Symbol, Set<State>>> tableTransition) {
        this.tableTransition = tableTransition;
    }

    public TransitionFunctionNFA() {
        this.tableTransition = new HashMap<>();
    }

    @Override
    public Set<State> transition(State state, Symbol symbol) {
        return Optional.ofNullable(tableTransition.get(state))
                .map(symbolSetMap -> new HashSet<>(symbolSetMap.getOrDefault(symbol, new HashSet<>())))
                .orElse(new HashSet<>());
    }

    @Override
    public Set<State> advancedTransition(State state, StringSymbols symbols) {
        if (symbols == null) {
            Set<State> states = new HashSet<>();
            states.add(state);
            return states;
        }
        Set<State> pStates = advancedTransition(state, symbols.getAllExpectLast());
        Set<State> rStates = new HashSet<>();
        for (State pState : pStates) {
            Set<State> transition = transition(pState, symbols.getLast());
            rStates.addAll(transition);
        }
        Set<State> resultStates = new HashSet<>();
        for (State rState : rStates) {
            resultStates.addAll(epsilonClosure(rState));
        }
        return resultStates;
    }


    public Set<State> epsilonClosure(State state) {
        Set<State> states = new HashSet<>();
        states.add(state);
        Set<State> eStates = transition(state, epsilon);
        if (eStates != null) {
            for (State eState : eStates) {
                states.addAll(epsilonClosure(eState));
            }
        }
        return states;
    }

    public Set<State> epsilonClosureWithVisited(Set<State> visited, State state) {
        Set<State> states = new HashSet<>();
        states.add(state);
        Set<State> eStates = transition(state, epsilon);
        if (eStates != null) {
            for (State eState : eStates) {
                if (visited.contains(eState)) {
                    continue;
                }
                visited.add(eState);
                states.addAll(epsilonClosureWithVisited(visited, eState));
            }
        }
        return states;
    }

    public void putToTable(State stateStart, Symbol symbol, Set<State> stateEnd) {
        Map<Symbol, Set<State>> oldMap = tableTransition.get(stateStart);
        Map<Symbol, Set<State>> newMap = Objects.requireNonNullElseGet(oldMap, HashMap::new);
        Set<State> states = newMap.get(symbol);
        if (states == null) {
            newMap.put(symbol, stateEnd);
        } else {
            states.addAll(stateEnd);
        }
        tableTransition.put(stateStart, newMap);
    }

    public void putToTable(State stateStart) {
        Map<Symbol, Set<State>> oldMap = tableTransition.get(stateStart);
        Map<Symbol, Set<State>> newMap = Objects.requireNonNullElseGet(oldMap, HashMap::new);

        tableTransition.put(stateStart, newMap);
    }

    public void putToTable(State stateStart, Symbol symbol, State... stateEnds) {
        putToTable(stateStart, symbol, new HashSet<>(Arrays.asList(stateEnds)));
    }

    public void putAll(TransitionFunctionNFA transitionFunctionNFA) {
        tableTransition.putAll(transitionFunctionNFA.getTableTransition());
    }

    @Override
    public String toString() {
        return tableTransition.entrySet().stream()
                .sorted(Map.Entry.comparingByKey())
                .flatMap(outerEntry ->
                        outerEntry.getValue().entrySet().stream()
                                .sorted(Map.Entry.comparingByKey())
                                .flatMap(innerEntry -> {
                                    State currentState = outerEntry.getKey();
                                    Symbol transitionSymbol = innerEntry.getKey();
                                    List<State> destinationStates = innerEntry.getValue().stream().sorted().toList();
                                    return Stream.of(String.format("(%s, %s) -> %s", currentState, transitionSymbol, destinationStates));
                                }))
                .collect(Collectors.joining("\n", "\n", ""));
    }
}
