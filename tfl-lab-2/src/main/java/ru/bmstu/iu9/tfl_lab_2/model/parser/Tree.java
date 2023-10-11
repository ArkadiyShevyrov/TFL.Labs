package ru.bmstu.iu9.tfl_lab_2.model.parser;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.ToString;
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
    }

    @Override
    public String toString() {
        return "Tree{" +
                "type=" + type + "\n"+
                ", value='" + value + '\'' + "\n"+
                ", children=" + children + "\n"+
                '}';
    }
}
