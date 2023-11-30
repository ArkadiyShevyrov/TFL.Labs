package ru.bmstu.iu9.tfl_lab_lib;

import ru.bmstu.iu9.tfl_lab_lib.automaton.Regex;

public class OptimizeRegex {
    public static Regex optimize(Regex regex) {
        switch (regex.getType()) {
            case ASTERISK -> {
                Regex optimize = optimize(regex.getLeft());
                if (optimize.getType() == Regex.Type.EMPTY) {
                    return new Regex(Regex.Type.EPSILON);
                }
                regex.setLeft(optimize);
                return regex;
            }
            case OR -> {
                Regex optimizeLeft = optimize(regex.getLeft());
                Regex optimizeRight = optimize(regex.getRight());
                if (optimizeLeft.getType() == Regex.Type.EMPTY) {
                    return optimizeRight;
                }
                if (optimizeRight.getType() == Regex.Type.EMPTY) {
                    return optimizeLeft;
                }
                regex.setLeft(optimizeLeft);
                regex.setRight(optimizeRight);
                return regex;
            }
            case CONCAT -> {
                Regex optimizeLeft = optimize(regex.getLeft());
                Regex optimizeRight = optimize(regex.getRight());
                if (optimizeLeft.getType() == Regex.Type.EPSILON) {
                    return optimizeRight;
                }
                if (optimizeRight.getType() == Regex.Type.EPSILON) {
                    return optimizeLeft;
                }
                if (optimizeLeft.getType() == Regex.Type.EMPTY) {
                    return optimizeLeft;
                }
                if (optimizeRight.getType() == Regex.Type.EMPTY) {
                    return optimizeRight;
                }
                regex.setLeft(optimizeLeft);
                regex.setRight(optimizeRight);
                return regex;
            }
            default -> {
                return regex;
            }
        }
    }
}
