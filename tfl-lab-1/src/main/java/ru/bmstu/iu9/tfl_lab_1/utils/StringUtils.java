package ru.bmstu.iu9.tfl_lab_1.utils;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_1.model.rest.SrsString;
import java.util.ArrayList;
import java.util.List;

@UtilityClass
public class StringUtils {
    public List<String> getAlphabetLetters(List<SrsString> srsStrings) {
        List<Character> alphabetLetters = new ArrayList<>();
        for (SrsString srsString : srsStrings) {
            String srsStr = srsString.getSrsString();
            for (int i = 0; i < srsStr.length(); i++) {
                char currentChar = srsStr.charAt(i);
                if (Character.isLetter(currentChar) && !alphabetLetters.contains(currentChar)) {
                    alphabetLetters.add(currentChar);
                }
            }
        }

        List<String> characters = new ArrayList<>();
        for (Character character : alphabetLetters) {
            characters.add(String.valueOf(character));
        }
        return characters;
    }

}
