package ru.bmstu.iu9.tfl_lab_2.model.parser.syntax;

import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.IterLexeme;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.Lexeme;
import java.util.List;

public class SyntaxIter implements Syntax {

    @Override
    public Tree parse(IterLexeme iterLexeme) {
        Tree parseOne = new SyntaxGroup().parse(iterLexeme);
        if (iterLexeme.getCurrent() != null &&
                iterLexeme.getCurrent().getType() == Lexeme.LexemeType.ITERATION) {
            Tree tree = new Tree(Tree.Type.ASTERISK, List.of(parseOne));
            while (iterLexeme.getCurrent() != null &&
                    iterLexeme.getCurrent().getType() == Lexeme.LexemeType.ITERATION) {
                iterLexeme.next();
                tree = new Tree(Tree.Type.ASTERISK, List.of(tree));
            }
            return tree;
        }
        return parseOne;
    }
}
