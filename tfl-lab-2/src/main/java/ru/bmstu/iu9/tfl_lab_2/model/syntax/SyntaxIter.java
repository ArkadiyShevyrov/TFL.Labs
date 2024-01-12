package ru.bmstu.iu9.tfl_lab_2.model.syntax;

import ru.bmstu.iu9.tfl_lab_2.model.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.lexeme.IterLexeme;
import ru.bmstu.iu9.tfl_lab_2.model.lexeme.Lexeme;

public class SyntaxIter implements Syntax {
    @Override
    public Tree parse(IterLexeme iterLexeme) {
        Tree parseOne = new SyntaxGroup().parse(iterLexeme);
        if (iterLexeme.getCurrent() != null &&
                iterLexeme.getCurrent().getType() == Lexeme.LexemeType.ITERATION) {
            Tree tree = new Tree(Tree.Type.ASTERISK, parseOne);
            iterLexeme.next();
            while (iterLexeme.getCurrent() != null &&
                    iterLexeme.getCurrent().getType() == Lexeme.LexemeType.ITERATION) {
                iterLexeme.next();
                tree = new Tree(Tree.Type.ASTERISK, tree);
            }
            return tree;
        }
        return parseOne;
    }
}
