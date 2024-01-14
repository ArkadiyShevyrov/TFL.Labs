package ru.bmstu.iu9.tfl_lab_lib.utils.generator;

import lombok.AllArgsConstructor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.*;
import ru.bmstu.iu9.tfl_lab_lib.model.grammer.*;
import ru.bmstu.iu9.tfl_lab_lib.utils.grammar.GrammarFollow;
import java.util.*;

@UtilityClass
public class LR0 {

    public static void main(String[] args) {
        Variable variableE = new Variable("E");
        Variable variableT = new Variable("T");

        Set<Variable> variables = new HashSet<>();
        variables.add(variableE);
        variables.add(variableT);

        Terminal terminalN = new Terminal("n");
        Terminal terminalPlus = new Terminal("+");
        Terminal terminalOpen = new Terminal("(");
        Terminal terminalClose = new Terminal(")");

        Set<Terminal> terminals = new HashSet<>();
        terminals.add(terminalN);
        terminals.add(terminalPlus);
        terminals.add(terminalOpen);
        terminals.add(terminalClose);

        Productions productions = new Productions();
        productions.putToTable(variableE,
                new GrammarString(variableE, terminalPlus, variableT),
                new GrammarString(variableT));
        productions.putToTable(variableT,
                new GrammarString(terminalN),
                new GrammarString(terminalOpen, variableE, terminalClose));

        CFGrammar cfGrammar = new CFGrammar(variables, terminals, productions, variableE);
        ResultLR0 resultLR0 = lr0(cfGrammar, new TerminalString("(n+n)+n"));
    }

    public ResultLR0 lr0(CFGrammar grammar, TerminalString terminalString) {
        CFGrammar replenishGrammar = replenishGrammar(grammar);
        DFA dfa = buildAutomaton(replenishGrammar);
        Map<Variable, Set<Terminal>> follows = GrammarFollow.constructFollow(replenishGrammar);
        Map<State, Map<SymbolGrammar, ParsingTableEntry>> stateMapMap = buildParsingTable(dfa, follows);
        ParsingTree parse = parse(stateMapMap);
        return new ResultLR0(parse);
    }

    public CFGrammar replenishGrammar(CFGrammar grammar) {
        Variable startVariable = grammar.getStartVariable();
        Variable newStartVariable = new Variable(startVariable.getName() + "0");


        Set<Variable> variables = new HashSet<>(grammar.getVariables());
        variables.add(newStartVariable);

        Set<Terminal> terminals = new HashSet<>(grammar.getTerminals());

        Productions productions = new Productions(grammar.getProductions());
        productions.putToTable(newStartVariable, new GrammarString(startVariable));

        return new CFGrammar(variables, terminals, productions, newStartVariable);
    }

    public DFA buildAutomaton(CFGrammar grammar) {
        NFA nfa = buildNFA(grammar);
        return buildDFA(nfa);
    }

    private DFA buildDFA(NFA nfa) {
        Set<State> states = new HashSet<>();
        Set<Symbol> symbols = new HashSet<>();
        Set<State> finalStates = new HashSet<>();
        TransitionFunctionDFA transitionFunction = new TransitionFunctionDFA();


        State initialState = nfa.getInitialState();
        Set<State> stateSet = nfa.getTransitionFunction().epsilonClosureWithVisited(new HashSet<>(), initialState);

        State startState = new State(stateSet);
        states.add(startState);

        Stack<State> stack = new Stack<>();
        stack.add(startState);
        Set<State> visited = new HashSet<>();
        while (!stack.isEmpty()) {
            State currentState = stack.pop();
            visited.add(currentState);
            for (Symbol symbol : nfa.getSymbols()) {
                Set<State> nextStates = new HashSet<>();
                for (State state : currentState.getValue().getSetState()) {
                    nextStates.addAll(nfa.getTransitionFunction().transition(state, symbol));
                }
                if (nextStates.isEmpty()) {
                    continue;
                }
                for (State state : nextStates) {
                    nextStates.addAll(nfa.getTransitionFunction().epsilonClosureWithVisited(new HashSet<>(), state));
                }
                State nextState = new State(nextStates);
                states.add(nextState);
                symbols.add(symbol);
                transitionFunction.putToTable(currentState, symbol, nextState);
                if (!visited.contains(nextState)) {
                    stack.add(nextState);
                }
            }
        }

        return new DFA(states, symbols, startState, finalStates, transitionFunction);
    }

    private NFA buildNFA(CFGrammar grammar) {
        Set<State> states = new HashSet<>();
        Set<Symbol> symbols = new HashSet<>();
        Set<State> finalStates = new HashSet<>();
        TransitionFunctionNFA transitionFunction = new TransitionFunctionNFA();

        Variable startVariable = grammar.getStartVariable();
        HashMap<Variable, List<GrammarString>> tableProductions = grammar
                .getProductions()
                .getTableProductions();
        GrammarString grammarStr = tableProductions
                .get(startVariable)
                .get(0);

        StateValueGrammar start = new StateValueGrammar(
                startVariable, grammarStr, 0);

        State startState = new State(start);
        states.add(startState);

        Stack<StateValueGrammar> stack = new Stack<>();
        stack.add(start);

        Set<StateValueGrammar> posetil = new HashSet<>();
        while (!stack.isEmpty()) {
            StateValueGrammar current = stack.pop();
            posetil.add(current);
            State currentState = new State(current);
            if (current.getCurrentIndex() < current.getGrammarString().size()) {
                GrammarUnit grammarUnit = current.grammarString.getGrammarUnits().get(current.currentIndex);

                StateValueGrammar next = new StateValueGrammar(
                        current.variable, current.grammarString, current.currentIndex + 1);
                SymbolGrammar symbol = new SymbolGrammar(grammarUnit);
                State nextState = new State(next);
                states.add(nextState);
                transitionFunction.putToTable(currentState, symbol, nextState);
                symbols.add(symbol);
                if (!posetil.contains(next)) {
                    stack.add(next);
                }

                if (grammarUnit instanceof Variable variable) {
                    List<GrammarString> grammarStrings = tableProductions.get(variable);
                    for (GrammarString grammarString : grammarStrings) {
                        StateValueGrammar nextEpsilon = new StateValueGrammar(
                                variable, grammarString, 0);
                        State nextEpsilonState = new State(nextEpsilon);
                        states.add(nextEpsilonState);
                        Symbol epsilon = new Symbol(Symbol.Type.EPSILON);
                        transitionFunction.putToTable(currentState, epsilon, nextEpsilonState);
                        if (!posetil.contains(nextEpsilon)) {
                            stack.add(nextEpsilon);
                        }
                    }
                }
            }
        }
        System.out.println();

        return new NFA(states, symbols, startState, finalStates, transitionFunction);
    }

    public Map<State, Map<SymbolGrammar, ParsingTableEntry>> buildParsingTable(DFA dfa, Map<Variable, Set<Terminal>> followGrammar) {
        Map<State, Map<SymbolGrammar, ParsingTableEntry>> table = new HashMap<>();

        for (State state : dfa.getStates()) {
            Map<SymbolGrammar, ParsingTableEntry> map = new HashMap<>();
            for (Symbol symbol : dfa.getSymbols()) {
                State transition = dfa.getTransitionFunction().transition(state, symbol);
                if (transition == null) {
                    continue;
                }
                if (symbol instanceof SymbolGrammar symbolGrammar) {
                    GrammarUnit value = symbolGrammar.getValue();
                    if (value instanceof Terminal) {
                        map.put(symbolGrammar, new ParsingTableEntry(ParsingTableEntry.Type.SHIFT, transition));
                    } else {
                        map.put(symbolGrammar, new ParsingTableEntry(ParsingTableEntry.Type.STATE, transition));
                    }
                }
            }
            StateValueGrammar stateValueGrammar = getStateValueGrammar(state);
            if (stateValueGrammar != null) {
                Variable variable = stateValueGrammar.getVariable();
                List<SymbolGrammar> symbolGrammars = followGrammar.get(variable).stream().map(SymbolGrammar::new).toList();
                for (SymbolGrammar symbolGrammar : symbolGrammars) {
                    map.put(symbolGrammar, new ParsingTableEntry(ParsingTableEntry.Type.REDUCE, variable, stateValueGrammar.getGrammarString()));
                }
            }
            table.put(state, map);
        }

        return table;
    }

    private boolean isDotLast(State state) {
        Set<State> setState = state.getValue().getSetState();
        for (State stateLocal : setState) {
            StateValue value = stateLocal.getValue();
            if (value instanceof StateValueGrammar stateValueGrammar) {
                if (stateValueGrammar.currentIndex == stateValueGrammar.grammarString.size()) {
                    return true;
                }
            }
        }
        return false;
    }
    private StateValueGrammar getStateValueGrammar(State state) {
        Set<State> setState = state.getValue().getSetState();
        for (State stateLocal : setState) {
            StateValue value = stateLocal.getValue();
            if (value instanceof StateValueGrammar stateValueGrammar) {
                if (stateValueGrammar.currentIndex == stateValueGrammar.grammarString.size()) {
                    return stateValueGrammar;
                }
            }
        }
        return null;
    }

    public ParsingTree parse(Map<State, Map<SymbolGrammar, ParsingTableEntry>> stateMapMap) {
        return null;

    }

    @Getter
    @EqualsAndHashCode(callSuper = false)
    class SymbolGrammar extends Symbol {
        private final GrammarUnit value;

        public SymbolGrammar(GrammarUnit value) {
            super(Type.VALUE);
            this.value = value;
        }

        @Override
        public String toString() {
            if (super.getType() == Type.VALUE) {
                return value.toString();
            }
            return super.toString();
        }
    }

    @Getter
    @EqualsAndHashCode(callSuper = false)
    class StateValueGrammar extends StateValue {
        private Variable variable;
        private GrammarString grammarString;
        private int currentIndex;

        public StateValueGrammar(Set<State> setState) {
            super.setType(Type.SET_STATE);
            super.setSetState(setState);
        }

        public StateValueGrammar(Variable variable, GrammarString grammarString, int currentIndex) {
            super.setType(Type.VALUE);
            this.variable = variable;
            this.grammarString = grammarString;
            this.currentIndex = currentIndex;
        }

        @Override
        public String toString() {
            if (super.getType() == Type.VALUE) {
                StringBuilder builder = new StringBuilder();
                builder.append(variable)
                        .append(" -> ");
                List<GrammarUnit> grammarUnits = grammarString.getGrammarUnits();
                for (int i = 0; i <= grammarUnits.size(); i++) {
                    if (i == grammarUnits.size()) {
                        if (i == currentIndex) {
                            builder.append(".");
                        }
                        break;
                    }
                    if (i == currentIndex) {
                        builder.append(".");
                    }
                    builder.append(grammarUnits.get(i));
                }
                return builder.toString();
            }
            return super.toString();
        }
    }

    @Getter
    public static class ParsingTableEntry {
        private Type type;

        private State state;

        private Variable variable;
        private GrammarString grammarString;

        public ParsingTableEntry(Type type, State state) {
            this.type = type;
            this.state = state;
        }

        public ParsingTableEntry(Type type, Variable variable, GrammarString grammarString) {
            this.type = type;
            this.variable = variable;
            this.grammarString = grammarString;
        }

        enum Type {
            STATE,
            SHIFT,
            REDUCE
        }
    }

    @AllArgsConstructor
    public static class ResultLR0 {
        private ParsingTree parsingTree;

        enum Type {
            PARSING_TREE
        }
    }
}
