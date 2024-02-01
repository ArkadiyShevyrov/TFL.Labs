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
    static final RegexLin emptyRegex = new RegexLin(Regex.Type.EMPTY);
    public static void main(String[] args) {
//        Regex regex = new Regex(
//                Regex.Type.CONCAT,
//                new Regex(
//                        Regex.Type.OR,
//                        new Regex(
//                                Regex.Type.CONCAT,
//                                new Regex("b"),
//                                new Regex("a")),
//                        new Regex("b")),
//                new Regex(
//                        Regex.Type.CONCAT,
//                        new Regex("a"),
//                        new Regex(
//                                Regex.Type.CONCAT,
//                                new Regex("a"),
//                                new Regex(
//                                        Regex.Type.ASTERISK,
//                                        new Regex(
//                                                Regex.Type.OR,
//                                                new Regex("a"),
//                                                new Regex(
//                                                        Regex.Type.CONCAT,
//                                                        new Regex("a"),
//                                                        new Regex("b")))))));
        Regex regex = new Regex(
                Regex.Type.ASTERISK,
                new Regex(
                        Regex.Type.CONCAT,
                        new Regex("c"),
                        new Regex("d")));
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
            if (regexLin.equals(emptyRegex)) {
                continue;
            }
            finalStates.add(new State(regexLin.toString()));
        }

        TransitionFunctionNFA transitionFunctionNFA = new TransitionFunctionNFA();
        for (RegexLin regexLin : combo.getFirsts()) {
            if (regexLin.equals(emptyRegex)) {
                finalStates.add(initialState);
                continue;
            }
            State stateNext = new State(regexLin.toString());
            Symbol symbol = new Symbol(regexLin.getValue());
            transitionFunctionNFA.putToTable(initialState, symbol, stateNext);
        }
        for (RegexLin regexLin : combo.getFollows().keySet()) {
            State stateStart = new State(regexLin.toString());
            for (RegexLin refLin : combo.getFollows().get(regexLin)) {
                if (refLin.equals(emptyRegex)) {
                    continue;
                }
                State stateNext = new State(refLin.toString());
                Symbol symbol = new Symbol(refLin.getValue());
                transitionFunctionNFA.putToTable(stateStart, symbol, stateNext);
            }
        }
        for (RegexLin regexLin : combo.getFirsts()) {
            if (regexLin.equals(emptyRegex)) {
                continue;
            }
            State state = new State(regexLin.toString());
            transitionFunctionNFA.putToTable(state);
        }
        for (RegexLin regexLin : combo.getLasts()) {
            if (regexLin.equals(emptyRegex)) {
                continue;
            }
            State state = new State(regexLin.toString());
            transitionFunctionNFA.putToTable(state);
        }

        states.addAll(transitionFunctionNFA.getTableTransition().keySet());

        return new NFA(states, symbols, initialState, finalStates, transitionFunctionNFA);
    }

    private Combo geCombo(RegexLin regex) {
        switch (regex.getType()) {
            case SYMBOL -> {
                return new Combo(
                        new HashSet<>(Set.of(regex)),
                        new HashSet<>(Set.of(regex)),
                        new HashMap<>());
            }
            case OR -> {
                Combo comboLeft = geCombo((RegexLin) regex.getLeft());
                Combo comboRight = geCombo((RegexLin) regex.getRight());

                Set<RegexLin> firsts = new HashSet<>();
                Set<RegexLin> lasts = new HashSet<>();
                Map<RegexLin, Set<RegexLin>> follows = new HashMap<>();

                firsts.addAll(Objects.requireNonNull(comboLeft).getFirsts());
                firsts.addAll(Objects.requireNonNull(comboRight).getFirsts());

                lasts.addAll(comboLeft.getLasts());
                lasts.addAll(comboRight.getLasts());

                follows.putAll(comboLeft.getFollows());
                follows.putAll(comboRight.getFollows());

                return new Combo(firsts, lasts, follows);
            }
            case CONCAT -> {
                Combo comboLeft = geCombo((RegexLin) regex.getLeft());
                Combo comboRight = geCombo((RegexLin) regex.getRight());

                Map<RegexLin, Set<RegexLin>> follows = new HashMap<>();

                follows.putAll(Objects.requireNonNull(comboLeft).getFollows());
                follows.putAll(Objects.requireNonNull(comboRight).getFollows());

                for (RegexLin last : comboLeft.getLasts()) {
                    if (last.equals(emptyRegex)) {
                        continue;
                    }
                    Set<RegexLin> firsts = new HashSet<>(comboRight.getFirsts());
                    firsts.remove(emptyRegex);
                    follows.put(last, firsts);
                }

                Set<RegexLin> firstsRight = comboRight.getFirsts();
                Set<RegexLin> firstsLeft = comboLeft.getFirsts();
                Set<RegexLin> lastsRight = comboRight.getLasts();
                Set<RegexLin> lastsLeft = comboLeft.getLasts();
                if (lastsRight.contains(emptyRegex)) {
                    lastsRight.addAll(lastsLeft);
                    if (!lastsLeft.contains(emptyRegex)) {
                        lastsRight.remove(emptyRegex);
                    }
                }
                if (firstsLeft.contains(emptyRegex)) {
                    firstsLeft.addAll(firstsRight);
                    if (!firstsRight.contains(emptyRegex)) {
                        firstsLeft.remove(emptyRegex);
                    }
                }
                return new Combo(firstsLeft, lastsRight, follows);
            }
            case ASTERISK -> {
                Combo combo = geCombo((RegexLin) regex.getLeft());

                Set<RegexLin> firsts = Objects.requireNonNull(combo).getFirsts();
                Set<RegexLin> lasts = Objects.requireNonNull(combo).getLasts();

                Map<RegexLin, Set<RegexLin>> follows = new HashMap<>(combo.getFollows());

                for (RegexLin last : lasts) {
                    follows.put(last, firsts);
                }

                firsts.add(emptyRegex);
                lasts.add(emptyRegex);

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
        Set<RegexLin> firsts;
        Set<RegexLin> lasts;
        Map<RegexLin, Set<RegexLin>> follows;

        @Override
        public String toString() {
            StringBuilder stringBuilder = new StringBuilder();
            for (RegexLin follow : follows.keySet()) {
                Set<RegexLin> Set = follows.get(follow);
                stringBuilder.append(follow);
                stringBuilder.append(Set);
                stringBuilder.append("\n");
            }
            return stringBuilder.toString();
        }
    }

}
