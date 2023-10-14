package ru.bmstu.iu9.tfl_lab_2.model.parser;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.ToString;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.Lexeme;
import java.util.List;

@Getter
public class Tree {
    private final Type type;
    private String value;
    private List<Tree> children;

    public Tree(Type type, List<Tree> children) {
        this.type = type;
        this.children = children;
    }

    public Tree(Type type, String value) {
        this.type = type;
        this.value = value;
    }

    public enum Type {
        OR,
        CONCAT,
        ASTERISK,
        SYMBOL,
        GROUP,
    }

    @Override
    public String toString() {
        switch (type) {
            case OR -> {
                return children.get(0) + "|" + children.get(1);
            }
            case CONCAT -> {
                return children.get(0).toString()  + children.get(1);
            }
            case SYMBOL -> {
                return value;
            }
            case ASTERISK -> {
                return children.get(0) + "*";
            }
            case GROUP -> {
                return "(" + children.get(0) + ")";
            }
            default -> {
                return "";
            }
        }
    }
}
