package ru.bmstu.iu9.tfl_lab_lib.model.grammer;

import lombok.AllArgsConstructor;
import lombok.Getter;
import java.util.List;

@Getter
@AllArgsConstructor
public class ParsingTree {
    List<ParsingTree> children;
    private Terminal terminal;
    private Type type;

    public enum Type {
        VARIABLE,
        TERMINAL,
    }
}
