package ru.bmstu.iu9.tfl_lab_2.model.parser.syntax;

import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.IterLexeme;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.Lexeme;
import java.util.List;

public class SyntaxGroup implements Syntax {
    @Override
    public Tree parse(IterLexeme iterLexeme) {
        if (iterLexeme.getCurrent() != null &&
                iterLexeme.getCurrent().getType() == Lexeme.LexemeType.SYMBOL) {
            String value = iterLexeme.getCurrent().getValue();
            iterLexeme.next();
            return new Tree(Tree.Type.SYMBOL, value);
        }
        if (iterLexeme.getCurrent() != null &&
                iterLexeme.getCurrent().getType() == Lexeme.LexemeType.OPEN_BRACKET) {
            iterLexeme.next();
            Tree parseOne = new SyntaxRegex().parse(iterLexeme);
            if (iterLexeme.getCurrent() == null ||
                    iterLexeme.getCurrent().getType() != Lexeme.LexemeType.CLOSE_BRACKET) {
                throw new RuntimeException();
            }
            iterLexeme.next();
            return new Tree(Tree.Type.GROUP, List.of(parseOne));
        }
        throw new RuntimeException();
    }
}
