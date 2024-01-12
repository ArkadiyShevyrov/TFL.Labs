package ru.bmstu.iu9.tfl_lab_2;

import lombok.experimental.UtilityClass;
import lombok.extern.slf4j.Slf4j;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import static ru.bmstu.iu9.tfl_lab_lib.model.Regex.Type.*;

@Slf4j
@UtilityClass
public class RandomRegexGenerator {
    public static void main(String[] args) {
        for (int i = 0; i < 100; i++) {
            log.info(generateRandomRegex(5, 10, 250).toString());
        }
    }

    public Regex generateRandomRegex(int alphabetSize, int starHeight, int maxLetters) {
        List<String> alphabet = generateRandomAlphabet(alphabetSize);
        return generateRandomRegex(alphabet, starHeight, maxLetters);
    }

    private Regex generateRandomRegex(List<String> alphabet, int starHeight, int maxLetters) {
        Regex.Type type;
        if (maxLetters < 2) {
            type = SYMBOL;
        } else {
            if (starHeight == 0) {
                type = pickRandomElement(List.of(SYMBOL, CONCAT, OR));
            } else {
                type = pickRandomElement(List.of(SYMBOL, CONCAT, OR, ASTERISK));
            }
        }
        int n = (maxLetters <= 1) ? 1 : new Random().nextInt(maxLetters - 1) + 1;
        return switch (type) {
            case SYMBOL -> new Regex(type, pickRandomElement(alphabet));
            case ASTERISK -> new Regex(type, generateRandomRegex(alphabet, starHeight - 1, maxLetters - 1));
            case CONCAT, OR -> new Regex(type,
                    generateRandomRegex(alphabet, starHeight, maxLetters - n),
                    generateRandomRegex(alphabet, starHeight, n));
            default -> null;
        };
    }

    private static List<String> generateRandomAlphabet(int alphabetSize) {
        List<String> alphabet = IntStream.range('a', 'z' + 1)
                .mapToObj(c -> String.valueOf((char) c))
                .collect(Collectors.toList());

        Collections.shuffle(alphabet);

        return alphabet.subList(0, alphabetSize);
    }

    public static <T> T pickRandomElement(List<T> list) {
        Random random = new Random();
        int randomIndex = random.nextInt(list.size());
        return list.get(randomIndex);
    }
}
