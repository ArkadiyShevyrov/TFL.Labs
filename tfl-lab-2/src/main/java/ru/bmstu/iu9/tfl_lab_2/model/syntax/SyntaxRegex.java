package ru.bmstu.iu9.tfl_lab_2.model.syntax;

import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_2.model.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.lexeme.IterLexeme;
import ru.bmstu.iu9.tfl_lab_2.model.lexeme.Lexeme;

@Getter
public class SyntaxRegex implements Syntax {
    @Override
    public Tree parse(IterLexeme iterLexeme) {
        Tree parseOne = new SyntaxConcat().parse(iterLexeme);
        Lexeme currentLexeme = iterLexeme.getCurrent();
        if (currentLexeme != null &&
                currentLexeme.getType() == Lexeme.LexemeType.OR) {
            iterLexeme.next();
            Tree parseTwo = new SyntaxRegex().parse(iterLexeme);
            return new Tree(Tree.Type.OR, parseOne, parseTwo);
        }
        return parseOne;
    }
}
