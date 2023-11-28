package ru.bmstu.iu9.tfl_lab_lib.automaton.model;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import java.io.Serializable;

@Slf4j
@Getter
@Setter
@AllArgsConstructor
public class Regex implements Serializable, Comparable {
    private Type type;
    private String value;
    private Regex left;
    private Regex right;

    public Regex(Type type, Regex left) {
        this.type = type;
        this.left = left;
    }

    public Regex(Type type, Regex left, Regex right) {
        this.type = type;
        this.left = left;
        this.right = right;
    }

    public Regex(Type type, String value) {
        this.type = type;
        this.value = value;
    }

    public Regex(String value) {
        this.type = Type.SYMBOL;
        this.value = value;
    }

    public Regex(Type type) {
        this.type = type;
    }

    public static String drawTree(Regex root) {
        return "\n" + printTree(root, "", false);
    }

    private static String printTree(Regex root, String prefix, boolean isLeft) {
        StringBuilder builder = new StringBuilder();
        if (root != null) {
            builder.append(prefix).append(isLeft ? "├── " : "└── ").append(root.getType())
                    .append(root.getValue() != null ? " " + root.getValue() : "").append("\n");
            String s1 = printTree(root.left, prefix + (isLeft ? "│   " : "    "), root.right != null);
            String s2 = printTree(root.right, prefix + (isLeft ? "│   " : "    "), false);
            builder.append(s1).append(s2);
        }
        return builder.toString();
    }

    @Override
    public String toString() {
        switch (type) {
            case OR -> {
                return left + "|" + right;
            }
            case CONCAT -> {
                if (left.getType() == Type.OR &&
                        right.getType() != Type.OR) {
                    return "(" + left + ")" + right;
                }
                if (right.getType() == Type.OR &&
                        left.getType() != Type.OR) {
                    return left + "(" + right + ")";
                }
                if (right.getType() == Type.OR &&
                        left.getType() == Type.OR) {
                    return "(" + left + ")" + "(" + right + ")";
                }
                return left + "" + right;
            }
            case SYMBOL -> {
                return value;
            }
            case ASTERISK -> {
                if (left.getType() == Type.SYMBOL) {
                    return left + "*";
                }
                return "(" + left + ")" + "*";
            }
            case EPSILON -> {
                return "ε";
            }
            case EMPTY -> {
                return "∅";
            }
            default -> {
                return "";
            }
        }
    }

    @Override
    public int compareTo(Object o) {
        Regex r = (Regex) o;
        if (this.type == r.type) {
            return this.toString().compareTo(r.toString());
        } else {
            return this.type.ordinal() - r.type.ordinal();
        }
    }

    public enum Type {
        EMPTY,
        EPSILON,
        SYMBOL,
        OR,
        CONCAT,
        ASTERISK,
    }
}
