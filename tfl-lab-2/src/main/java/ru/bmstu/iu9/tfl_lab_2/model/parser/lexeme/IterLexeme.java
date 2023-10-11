package ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme;

import java.util.ArrayList;
import java.util.List;

public class IterLexeme {
    private final List<Lexeme> lexemes;
    private int position;
    private final int size;

    public IterLexeme(List<Lexeme> lexemes) {
        this.lexemes = new ArrayList<>(lexemes);
        this.position = 0;
        this.size = lexemes.size();
    }

    public Lexeme getCurrent() {
        if (position < size) {
            return lexemes.get(position);
        }
        return null;
    }

    public void next() {
        position++;
    }

}
