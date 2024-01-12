package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.RegexLin;

public class ConvertRegexToRegexLin {
    private int currentNumber = 1;

    public RegexLin convert(Regex regex) {
        return switch (regex.getType()) {
            case SYMBOL -> new RegexLin(regex, currentNumber++);
            case CONCAT -> new RegexLin(
                    Regex.Type.CONCAT,
                    convert(regex.getLeft()),
                    convert(regex.getRight())
            );
            case OR -> new RegexLin(
                    Regex.Type.OR,
                    convert(regex.getLeft()),
                    convert(regex.getRight())
            );
            case ASTERISK -> new RegexLin(
                    Regex.Type.ASTERISK,
                    convert(regex.getLeft())
            );
            default -> null;
        };
    }
}
