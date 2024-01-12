package ru.bmstu.iu9.tfl_lab_2.model.syntax;

import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_2.model.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.lexeme.IterLexeme;
import ru.bmstu.iu9.tfl_lab_2.model.lexeme.Lexeme;

@Getter
public class SyntaxConcat implements Syntax {
    @Override
    public Tree parse(IterLexeme iterLexeme) {
        Tree parseOne = new SyntaxIter().parse(iterLexeme);
        Lexeme currentLexeme = iterLexeme.getCurrent();
        if (currentLexeme != null &&
                (currentLexeme.getType() == Lexeme.LexemeType.OPEN_BRACKET ||
                        currentLexeme.getType() == Lexeme.LexemeType.SYMBOL)) {
            Tree parseTwo = new SyntaxConcat().parse(iterLexeme);
            return new Tree(Tree.Type.CONCAT, parseOne, parseTwo);
        }
        return parseOne;
    }
}
