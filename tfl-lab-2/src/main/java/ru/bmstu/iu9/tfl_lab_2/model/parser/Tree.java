package ru.bmstu.iu9.tfl_lab_2.model.parser;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import java.io.Serializable;

@Slf4j
@Getter
@Setter
@AllArgsConstructor
public class Tree implements Serializable {
    private final Type type;
    private String value;

    private Tree left;
    private Tree right;

    public Tree(Type type) {
        this.type = type;
    }

    public Tree(Type type, Tree left) {
        this.type = type;
        this.left = left;
    }

    public Tree(Type type, Tree left, Tree right) {
        this.type = type;
        this.left = left;
        this.right = right;
    }

    public Tree(Type type, String value) {
        this.type = type;
        this.value = value;
    }

    public static void drawTree(Tree root) {
        printTree(root, "", true);
    }

    private static void printTree(Tree root, String prefix, boolean isLeft) {
        if (root != null) {
            log.info(prefix + (isLeft ? "├── " : "└── ") + root.getType() +
                    (root.getValue() != null ? " " + root.getValue() : ""));
            printTree(root.left, prefix + (isLeft ? "│   " : "    "), true);
            printTree(root.right, prefix + (isLeft ? "│   " : "    "), false);
        }
    }

    @Override
    public String toString() {
        switch (type) {
            case OR -> {
                return left + "|" + right;
            }
            case CONCAT -> {
                return left + "" + right;
            }
            case SYMBOL -> {
                return value;
            }
            case ASTERISK -> {
                return left + "*";
            }
            case GROUP -> {
                return "(" + left + ")";
            }
            default -> {
                return "";
            }

        }
    }

    public enum Type {
        OR,
        CONCAT,
        ASTERISK,
        SYMBOL,
        GROUP;
    }
}
