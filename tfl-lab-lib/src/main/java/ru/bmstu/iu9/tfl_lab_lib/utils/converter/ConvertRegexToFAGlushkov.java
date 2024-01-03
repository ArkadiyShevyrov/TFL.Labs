package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.RegexLin;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.TransitionFunctionNFA;
import java.util.*;

@UtilityClass
public class ConvertRegexToFAGlushkov {
    public static void main(String[] args) {
        Regex regex = new Regex(
                Regex.Type.CONCAT,
                new Regex(
                        Regex.Type.OR,
                        new Regex(
                                Regex.Type.CONCAT,
                                new Regex("b"),
                                new Regex("a")),
                        new Regex("b")),
                new Regex(
                        Regex.Type.CONCAT,
                        new Regex("a"),
                        new Regex(
                                Regex.Type.CONCAT,
                                new Regex("a"),
                                new Regex(
                                        Regex.Type.ASTERISK,
                                        new Regex(
                                                Regex.Type.OR,
                                                new Regex("a"),
                                                new Regex(
                                                        Regex.Type.CONCAT,
                                                        new Regex("a"),
                                                        new Regex("b")))))));
        NFA convert = convert(regex);
        System.out.println();
    }

    public NFA convert(Regex regex) {
        ConvertRegexToRegexLin convertRegexToRegexLin = new ConvertRegexToRegexLin();
        RegexLin convert = convertRegexToRegexLin.convert(regex);
        Combo combo = geCombo(convert);

        Set<State> states = new HashSet<>();
        for (RegexLin regexLin : combo.getFollows().keySet()) {
            states.add(new State(regexLin.toString()));
        }
        State initialState = new State("S0");
        states.add(initialState);

        Set<Symbol> symbols = new HashSet<>();
        for (RegexLin regexLin : combo.getFollows().keySet()) {
            symbols.add(new Symbol(regexLin.getValue()));
        }

        Set<State> finalStates = new HashSet<>();
        for (RegexLin regexLin : combo.getLasts()) {
            finalStates.add(new State(regexLin.toString()));
        }

        TransitionFunctionNFA transitionFunctionNFA = new TransitionFunctionNFA();
        for (RegexLin regexLin : combo.getFirsts()) {
            State stateNext = new State(regexLin.toString());
            Symbol symbol = new Symbol(regexLin.getValue());
            transitionFunctionNFA.putToTable(initialState, symbol, stateNext);
        }
        for (RegexLin regexLin : combo.getFollows().keySet()) {
            State stateStart = new State(regexLin.toString());
            for (RegexLin refLin : combo.getFollows().get(regexLin)) {
                State stateNext = new State(refLin.toString());
                Symbol symbol = new Symbol(refLin.getValue());
                transitionFunctionNFA.putToTable(stateStart, symbol, stateNext);
            }
        }

        return new NFA(states, symbols, initialState, finalStates, transitionFunctionNFA);
    }

    private Combo geCombo(RegexLin regex) {
        switch (regex.getType()) {
            case SYMBOL -> {
                return new Combo(
                        List.of(regex),
                        List.of(regex),
                        new HashMap<>());
            }
            case OR -> {
                Combo comboLeft = geCombo((RegexLin) regex.getLeft());
                Combo comboRight = geCombo((RegexLin) regex.getRight());

                List<RegexLin> firsts = new ArrayList<>();
                List<RegexLin> lasts = new ArrayList<>();
                Map<RegexLin, List<RegexLin>> follows = new HashMap<>();

                firsts.addAll(comboLeft.getFirsts());
                firsts.addAll(comboRight.getFirsts());

                lasts.addAll(comboLeft.getLasts());
                lasts.addAll(comboRight.getLasts());

                follows.putAll(comboLeft.getFollows());
                follows.putAll(comboRight.getFollows());

                return new Combo(firsts, lasts, follows);
            }
            case CONCAT -> {
                Combo comboLeft = geCombo((RegexLin) regex.getLeft());
                Combo comboRight = geCombo((RegexLin) regex.getRight());

                Map<RegexLin, List<RegexLin>> follows = new HashMap<>();

                follows.putAll(comboLeft.getFollows());
                follows.putAll(comboRight.getFollows());

                for (RegexLin last : comboLeft.getLasts()) {
                    follows.put(last, comboRight.getFirsts());
                }

                List<RegexLin> lasts = comboRight.getLasts();
                List<RegexLin> firsts = comboLeft.getFirsts();
                if (regex.getRight().getType() == Regex.Type.ASTERISK) {
                    lasts.addAll(firsts);
                }
                if (regex.getLeft().getType() == Regex.Type.ASTERISK) {
                    firsts.addAll(lasts);
                }

                return new Combo(firsts, lasts, follows);
            }
            case ASTERISK -> {
                Combo combo = geCombo((RegexLin) regex.getLeft());

                List<RegexLin> firsts = combo.getFirsts();
                List<RegexLin> lasts = combo.getLasts();

                Map<RegexLin, List<RegexLin>> follows = new HashMap<>(combo.getFollows());

                for (RegexLin last : lasts) {
                    follows.put(last, firsts);
                }

                return new Combo(firsts, lasts, follows);
            }
            default -> {
                return null;
            }
        }
    }

    @Getter
    @AllArgsConstructor
    public static class Combo {
        List<RegexLin> firsts;
        List<RegexLin> lasts;
        Map<RegexLin, List<RegexLin>> follows;

        @Override
        public String toString() {
            StringBuilder stringBuilder = new StringBuilder();
            for (RegexLin follow : follows.keySet()) {
                List<RegexLin> list = follows.get(follow);
                stringBuilder.append(follow);
                stringBuilder.append(list);
                stringBuilder.append("\n");
            }
            return stringBuilder.toString();
        }
    }

}
