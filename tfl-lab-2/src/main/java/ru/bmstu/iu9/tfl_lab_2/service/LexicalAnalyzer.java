package ru.bmstu.iu9.tfl_lab_2.service;

import lombok.extern.slf4j.Slf4j;
import org.springframework.boot.CommandLineRunner;
import org.springframework.stereotype.Service;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.Lexeme;
import java.util.ArrayList;
import java.util.List;

@Slf4j
@Service
public class LexicalAnalyzer implements CommandLineRunner {

    public List<Lexeme> lexicalAnalyze(String date) {
        List<Lexeme> lexemes = new ArrayList<>();
        for (int i = 0; i < date.length(); i++) {
            String c = String.valueOf(date.charAt(i));
            lexemes.add(new Lexeme(c));
        }
        return lexemes;
    }

    @Override
    public void run(String... args) {
        List<Lexeme> lexemes = lexicalAnalyze("(ab9|8c)**");
        log.info(lexemes.toString());
    }
}
