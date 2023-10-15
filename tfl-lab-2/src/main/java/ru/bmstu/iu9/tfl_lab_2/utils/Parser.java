package ru.bmstu.iu9.tfl_lab_2.utils;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.IterLexeme;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.Lexeme;
import ru.bmstu.iu9.tfl_lab_2.model.parser.syntax.SyntaxRegex;
import java.util.ArrayList;
import java.util.List;

@UtilityClass
public class Parser {

    public Tree parser(String data) {
        return syntacticalAnalyze(lexicalAnalyze(data));
    }

    private IterLexeme lexicalAnalyze(String date) {
        List<Lexeme> lexemes = new ArrayList<>();
        for (int i = 0; i < date.length(); i++) {
            String c = String.valueOf(date.charAt(i));
            lexemes.add(new Lexeme(c));
        }
        return new IterLexeme(lexemes);
    }

    private Tree syntacticalAnalyze(IterLexeme lexemes) {
        return new SyntaxRegex().parse(lexemes);
    }
}
