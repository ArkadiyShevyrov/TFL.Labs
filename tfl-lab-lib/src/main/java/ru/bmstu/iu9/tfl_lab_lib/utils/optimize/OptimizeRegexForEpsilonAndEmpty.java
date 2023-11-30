package ru.bmstu.iu9.tfl_lab_lib.utils.optimize;

import ru.bmstu.iu9.tfl_lab_lib.model.Regex;

public class OptimizeRegexForEpsilonAndEmpty {
    private final Regex empty = new Regex(Regex.Type.EMPTY);
    private final Regex epsilon = new Regex(Regex.Type.EPSILON);

    public Regex optimize(Regex regex) {
        switch (regex.getType()) {
            case ASTERISK -> {
                Regex optimize = optimize(regex.getLeft());
                if (optimize.getType() == Regex.Type.EMPTY) {
                    return epsilon;
                }
                regex.setLeft(optimize);
                return regex;
            }
            case OR -> {
                Regex left = optimize(regex.getLeft());
                Regex right = optimize(regex.getRight());
                if (left.getType() == Regex.Type.EMPTY) {
                    return right;
                }
                if (right.getType() == Regex.Type.EMPTY) {
                    return left;
                }
                regex.setLeft(left);
                regex.setRight(right);
                return regex;
            }
            case CONCAT -> {
                Regex left = optimize(regex.getLeft());
                Regex right = optimize(regex.getRight());
                if (left.getType() == Regex.Type.EPSILON) {
                    return right;
                }
                if (right.getType() == Regex.Type.EPSILON) {
                    return left;
                }
                if (left.getType() == Regex.Type.EMPTY) {
                    return empty;
                }
                if (right.getType() == Regex.Type.EMPTY) {
                    return empty;
                }
                regex.setLeft(left);
                regex.setRight(right);
                return regex;
            }
            default -> {
                return regex;
            }
        }
    }
}
