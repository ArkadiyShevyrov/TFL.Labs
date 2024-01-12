package ru.bmstu.iu9.tfl_lab_2.model.syntax;

import ru.bmstu.iu9.tfl_lab_2.model.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.lexeme.IterLexeme;

public interface Syntax {
    Tree parse(IterLexeme iterLexeme);
}
