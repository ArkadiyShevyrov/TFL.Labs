package ru.bmstu.iu9.tfl_lab_lib.utils;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import java.util.List;

@UtilityClass
public class RegexUtils {
    private final Regex empty = new Regex(Regex.Type.EMPTY);

    public Regex combinateRegex(List<Regex> regexes) {
        if (regexes.size() == 0) {
            return empty;
        }
        if (regexes.size() == 1) {
            return regexes.get(0);
        }
        Regex res = new Regex(Regex.Type.OR, regexes.get(0));
        Regex current = res;
        for (int i = 1; i < regexes.size(); i++) {
            Regex regex = regexes.get(i);
            if (i == regexes.size() - 1) {
                current.setRight(regex);
                break;
            }
            Regex right = new Regex(Regex.Type.OR, regex);
            current.setRight(right);
            current = right;
        }
        return res;
    }
}
