package ru.bmstu.iu9.tfl_lab_2.controller;

import io.swagger.v3.oas.annotations.Operation;
import io.swagger.v3.oas.annotations.tags.Tag;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import ru.bmstu.iu9.tfl_lab_2.model.parser.lexeme.Lexeme;
import ru.bmstu.iu9.tfl_lab_2.service.LexicalAnalyzer;
import java.util.List;

@Slf4j
@Tag(name = "Lab2", description = "Lab 2 description")
@RestController
@RequestMapping("/rest/lab-2")
@RequiredArgsConstructor
public class CController {

    private final LexicalAnalyzer lexicalAnalyzer;


    @Operation(description = "")
    @PostMapping(value = "/ss")
    public ResponseEntity<String> create(
    ) {
        List<Lexeme> lexemes = lexicalAnalyzer.lexicalAnalyze("asd");
        log.info(String.valueOf(lexemes.size()));
        return ResponseEntity.ok().body("");
    }
}
