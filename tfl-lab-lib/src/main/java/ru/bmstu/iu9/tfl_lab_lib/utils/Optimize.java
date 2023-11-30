package ru.bmstu.iu9.tfl_lab_lib.utils;

import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.utils.optimize.OptimizeRegexForEpsilonAndEmpty;

public class Optimize {

    public Regex optimizeRegexForEpsilonAndEmpty(Regex regex) {
        return OptimizeRegexForEpsilonAndEmpty.optimize(regex);
    }
}
