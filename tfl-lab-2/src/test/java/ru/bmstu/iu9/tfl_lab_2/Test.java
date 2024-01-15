package ru.bmstu.iu9.tfl_lab_2;

import lombok.extern.slf4j.Slf4j;
import ru.bmstu.iu9.tfl_lab_2.service.OptimizationService;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertRegexToFAGlushkov;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertTableTransitionToReachabilityMatrix;
import java.util.*;

@Slf4j
public class Test {
    private static final int countRegex = 1000;
    private static final int countWord = 1000;
    public static void main(String[] args) {
        boolean flag = true;
        for (int i = 0; i < countRegex; i++) {
            boolean b = randomReg();
            if (!b) {
                flag = false;
                break;
            }
        }
        log.info(String.valueOf(flag));
    }

    public static boolean randomReg() {
        Regex randomRegex = RandomRegexGenerator.generateRandomRegex(5, 2, 100);
        OptimizationService optimizationService = new OptimizationService();
        String optimizationRegex = optimizationService.optimization(randomRegex.toString());
        log.info("Random regex: " + randomRegex);
        log.info("Optimization regex: " + optimizationRegex);

        NFA nfa = ConvertRegexToFAGlushkov.convert(randomRegex);

        log.debug(nfa.getTransitionFunction().toString());
        log.debug(Arrays.toString(nfa.getStates().toArray()));
        Map<State, Set<State>> convert = ConvertTableTransitionToReachabilityMatrix.convert(nfa.getTransitionFunction().getTableTransition());
        List<String> words = new ArrayList<>();
        for (int i = 0; i < countWord; i++) {
//            String s = randomWord(nfa, convert) + "]";
            String s = randomWord(nfa, convert);
            words.add(s);
        }

        boolean flag = true;
        for (String word : words) {
//            log.info(word);
            boolean matchesRandom = word.matches(randomRegex.toString());
            if (!matchesRandom) {
                log.info("Хмм");
            }

            boolean matchesOptimize = word.matches(optimizationRegex);
            if (!matchesOptimize) {
                log.info("Хмм");
            }
            boolean a = matchesRandom && matchesOptimize;
            if (!a) {
                flag = false;
                log.info(word);
                break;
            }
        }
        return flag;
    }

    public static String randomWord(NFA nfa, Map<State, Set<State>> convert) {
        StringBuilder stringBuilder = new StringBuilder();
        State initialState = nfa.getInitialState();
        Set<State> finalStates = nfa.getFinalStates();
        for (int i = 0; i < 200; i++) {
            if (i > 100 && finalStates.contains(initialState)) {
                break;
            }
            Set<State> statesNext = convert.get(initialState);
            if (statesNext.isEmpty()) {
                break;
            }
            State randomState = getRandomState(statesNext);

            Set<Symbol> transitionSymbols = findTransitionSymbols(nfa.getTransitionFunction().getTableTransition(), initialState, randomState);
            List<Symbol> symbols = transitionSymbols.stream().toList();
            Symbol symbol = symbols.get(0);
            stringBuilder.append(symbol.toString());
            initialState = randomState;
            if (finalStates.contains(initialState)) {
                Random random = new Random();
                int i1 = random.nextInt(100);
                if (i1 > 90) {
                    break;
                }
            }
        }

        return stringBuilder.toString();
    }

    public static State getRandomState(Set<State> states) {
        List<State> statesList = new ArrayList<>(states);
        Random random = new Random();
        return statesList.get(random.nextInt(statesList.size()));
    }

    // Функция для поиска символов, по которым возможен переход из initialState в targetState
    public static Set<Symbol> findTransitionSymbols(
            Map<State, Map<Symbol, Set<State>>> tableTransition,
            State initialState, State targetState) {

        Set<Symbol> transitionSymbols = new HashSet<>();

        // Проверяем наличие начального состояния в таблице переходов
        if (tableTransition.containsKey(initialState)) {
            Map<Symbol, Set<State>> transitionMap = tableTransition.get(initialState);

            // Ищем символы, по которым возможен переход в targetState
            for (Map.Entry<Symbol, Set<State>> entry : transitionMap.entrySet()) {
                if (entry.getValue().contains(targetState)) {
                    transitionSymbols.add(entry.getKey());
                }
            }
        }

        return transitionSymbols;
    }
}
