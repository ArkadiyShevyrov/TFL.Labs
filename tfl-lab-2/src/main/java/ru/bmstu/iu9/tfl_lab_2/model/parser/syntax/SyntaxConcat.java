package ru.bmstu.iu9.tfl_lab_2.model.parser.syntax;

import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.Lexeme;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.IterLexeme;
import java.util.List;

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
            return new Tree(Tree.Type.CONCAT, List.of(parseOne, parseTwo));
        }
        return parseOne;
    }
}
