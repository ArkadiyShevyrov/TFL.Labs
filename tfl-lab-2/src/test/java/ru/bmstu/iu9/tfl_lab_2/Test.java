package ru.bmstu.iu9.tfl_lab_2;

import lombok.extern.slf4j.Slf4j;
import org.springframework.util.StopWatch;
import ru.bmstu.iu9.tfl_lab_2.service.OptimizationService;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.State;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.Symbol;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertRegexToFAGlushkov;
import ru.bmstu.iu9.tfl_lab_lib.utils.converter.ConvertTableTransitionToReachabilityMatrix;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@Slf4j
public class Test {
    public static void main(String[] args) {
        Regex randomRegex = RandomRegexGenerator.generateRandomRegex(10, 5, 200);

        OptimizationService optimizationService = new OptimizationService();
        String optimizationRegex = optimizationService.optimization(randomRegex.toString());
        log.info("Random regex: " + randomRegex);
        log.info("Optimization regex: " + optimizationRegex);

        NFA nfa = ConvertRegexToFAGlushkov.convert(randomRegex);


        log.info(nfa.getTransitionFunction().toString());
        log.info(Arrays.toString(nfa.getStates().toArray()));
        Map<State, Set<State>> convert = ConvertTableTransitionToReachabilityMatrix.convert(nfa.getTransitionFunction().getTableTransition());

        List<String> words = new ArrayList<>();
        for (int i = 0; i < 100; i++) {
//            String s = randomWord(nfa, convert) + "]";
            String s = randomWord(nfa, convert);
            words.add(s);
        }

        for (String word : words) {
            Pattern patternRandom = Pattern.compile(randomRegex.toString());
            Matcher matcherRandom = patternRandom.matcher(word);
            StopWatch stopWatchRandom = new StopWatch();
            stopWatchRandom.start();
            boolean matchesRandom = matcherRandom.matches();
            stopWatchRandom.stop();


            Pattern patternOptimize = Pattern.compile(optimizationRegex);
            Matcher matcherOptimize = patternOptimize.matcher(word);
            StopWatch stopWatchOptimize = new StopWatch();
            stopWatchOptimize.start();
            boolean matchesOptimize = matcherOptimize.matches();
            stopWatchOptimize.stop();
            if (matchesRandom && matchesOptimize) {
                log.info("Слово \"" + word + "\"" + "\n" +
                        "Регулярное выражение базовое: " + randomRegex + "\n" +
                        "Регулярное выражение оптимизированное: " + optimizationRegex + "\n" +
                        "Слово соответствует регулярному выражению.\n" +
                        "Заняло времени базовое: " + stopWatchRandom.getTotalTimeNanos() + "\n" +
                        "Заняло времени оптимизированное: " + stopWatchOptimize.getTotalTimeNanos() + "\n");
            } else {
                log.info("Слово \"" + word + "\"" + "\n" +
                        "Регулярное выражение базовое: " + randomRegex + "\n" +
                        "Регулярное выражение оптимизированное: " + optimizationRegex + "\n" +
                        "Слово не соответствует регулярному выражению.\n" +
                        "Заняло времени базовое: " + stopWatchRandom.getTotalTimeNanos() + "\n" +
                        "Заняло времени оптимизированное: " + stopWatchOptimize.getTotalTimeNanos() + "\n");
            }
        }
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
