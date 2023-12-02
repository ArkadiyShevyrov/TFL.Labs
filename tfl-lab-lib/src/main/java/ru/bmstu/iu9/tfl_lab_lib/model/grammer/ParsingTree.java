package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.Arrays;
import java.util.List;

@Getter
@AllArgsConstructor
public class ParsingTree {
    private Type type;
    private List<ParsingTree> children;
    private Terminal terminal;
    private Variable variable;

    public ParsingTree(Variable variable, List<ParsingTree> children) {
        this.variable = variable;
        this.type = Type.VARIABLE;
        this.children = children;
    }

    public ParsingTree(Terminal terminal) {
        this.type = Type.TERMINAL;
        this.terminal = terminal;
    }

    public int length() {
        switch (type) {
            case TERMINAL -> {
                if (terminal.getType() == Terminal.Type.STRING) {
                    return 1;
                } else {
                    return 0;
                }
            }
            case VARIABLE -> {
                int length = 0;
                for (ParsingTree parsingTree : children) {
                    length += parsingTree.length();
                }
                return length;
            }
            default -> {
                return 0;
            }
        }
    }

    @Override
    public String toString() {
        return switch (type) {
            case TERMINAL -> terminal.toString();
            case VARIABLE -> Arrays.toString(children.toArray());
        };
    }

    public String drawTree(ParsingTree tree) {
        return "\n" + printTree(tree, "", false);
    }

    private String printTree(ParsingTree tree, String prefix, boolean isFirst) {
        StringBuilder builder = new StringBuilder();
        if (tree != null) {
            builder.append(prefix).append(isFirst ? "├── " : "└── ")
                    .append(tree.getType() == Type.VARIABLE ? tree.variable : "")
                    .append(tree.getType() == Type.TERMINAL ? tree.terminal : "")
                    .append("\n");
            if (tree.children != null) {
                for (int i = 0; i < tree.children.size(); i++) {
                    if (i == 0) {
                        builder.append(printTree(tree.children.get(0), prefix + (isFirst ? "│   " : "    "), tree.children.size() > 1));
                    } else {
                        builder.append(printTree(tree.children.get(i), prefix + (isFirst ? "│   " : "    "), false));
                    }
                }
            }
        }
        return builder.toString();
    }

    public enum Type {
        VARIABLE,
        TERMINAL,
    }
}
