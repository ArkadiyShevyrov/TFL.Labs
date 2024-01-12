package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import lombok.experimental.UtilityClass;
import lombok.extern.slf4j.Slf4j;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.TransitionFunctionNFA;
import java.util.*;

@Slf4j
@UtilityClass
public class ConvertTableTransitionToReachabilityMatrix {
    public static void main(String[] args) {
        State state1 = new State("s1");
        State state2 = new State("s2");
        State state3 = new State("s3");
        State state4 = new State("s4");
        Symbol symbolA = new Symbol("a");
        Symbol symbolB = new Symbol("b");
        TransitionFunctionNFA transitionFunctionNFA = new TransitionFunctionNFA();
        transitionFunctionNFA.putToTable(state1, symbolA, state2);
        transitionFunctionNFA.putToTable(state1, symbolB, state3);
        transitionFunctionNFA.putToTable(state3, symbolA, state4);
        transitionFunctionNFA.putToTable(state3, symbolB, state2);
        transitionFunctionNFA.putToTable(state4, symbolA, state3);
        transitionFunctionNFA.putToTable(state2);
        convert(transitionFunctionNFA.getTableTransition());
    }

    public Map<State, Set<State>> convert(Map<State, Map<Symbol, Set<State>>> tableTransition) {
        Map<State, Set<State>> reachabilityMatrix = new HashMap<>();

        Map<State, Set<State>> stateSetMap = s1(tableTransition);
        IntStateMapping intStateMapping = stateMapping(stateSetMap.keySet());

        int size = stateSetMap.size();
        int[][] A1 = getA0(stateSetMap, intStateMapping, size);
        List<int[][]> As = new ArrayList<>();
        As.add(A1);
        for (int k = 2; k < size; k++) {
            int[][] ints = MatrixPower.matrixPower(A1, k);
            As.add(ints);
        }

        int[][] ints = MatrixPower.matrixDisjunction(As);

        for (int i = 0; i < size; i++) {
            State state = intStateMapping.getState(i);
            Set<State> statesNext = new HashSet<>();
            for (int j = 0; j < size; j++) {
                int i1 = ints[i][j];
                if (i1 == 1) {
                    statesNext.add(intStateMapping.getState(j));
                }
            }
            reachabilityMatrix.put(state, statesNext);
        }

        return stateSetMap;
    }

    private int[][] getA0(Map<State, Set<State>> stateSetMap, IntStateMapping intStateMapping, int size) {

        int[][] A = new int[size][size];
        for (int i = 0; i < size; i++) {
            State state = intStateMapping.getState(i);
            Set<State> statesNext = stateSetMap.get(state);
            List<Integer> ints = new ArrayList<>();

            if (statesNext != null && !statesNext.isEmpty()) {
                for (State stateNext : statesNext) {
                    Integer anInt = intStateMapping.getInt(stateNext);
                    ints.add(anInt);
                }

                for (Integer integer : ints) {
                    A[i][integer] = 1;
                }
            }
        }
        return A;
    }


    private IntStateMapping stateMapping(Set<State> states) {
        IntStateMapping intStateMapping = new IntStateMapping();

        int count = 0;
        for (State state : states) {
            intStateMapping.addMapping(count++, state);
        }

        return intStateMapping;
    }

    private Map<State, Set<State>> s1(Map<State, Map<Symbol, Set<State>>> tableTransition) {
        Map<State, Set<State>> tableStates = new HashMap<>();

        for (State state : tableTransition.keySet()) {
            Map<Symbol, Set<State>> symbolSetMap = tableTransition.get(state);
            Set<State> statesNext = new HashSet<>();
            for (Symbol symbol : symbolSetMap.keySet()) {
                Set<State> statesC = symbolSetMap.get(symbol);
                statesNext.addAll(statesC);
            }
            tableStates.put(state, statesNext);
        }

        return tableStates;
    }

    public class IntStateMapping {
        private final Map<Integer, State> intToStateMap;
        private final Map<State, Integer> stateToIntMap;

        public IntStateMapping() {
            intToStateMap = new HashMap<>();
            stateToIntMap = new HashMap<>();
        }

        public void addMapping(int intValue, State stateValue) {
            intToStateMap.put(intValue, stateValue);
            stateToIntMap.put(stateValue, intValue);
        }

        public State getState(int intValue) {
            return intToStateMap.get(intValue);
        }

        public Integer getInt(State stateValue) {
            return stateToIntMap.get(stateValue);
        }
    }
}
