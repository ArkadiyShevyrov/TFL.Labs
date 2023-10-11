package ru.bmstu.iu9.tfl_lab_2.model.parser.syntax;

import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.IterLexeme;

public interface Syntax {
    Tree parse(IterLexeme iterLexeme);
}
