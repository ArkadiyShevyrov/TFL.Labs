package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.List;

@Getter
@AllArgsConstructor
public class ParsingTree {
    private Type type;
    private List<ParsingTree> children;
    private Terminal terminal;

    public ParsingTree(List<ParsingTree> children) {
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

    public enum Type {
        VARIABLE,
        TERMINAL,
    }
}
