package ru.bmstu.iu9.tfl_lab_2.controller;

import io.swagger.v3.oas.annotations.Operation;
import io.swagger.v3.oas.annotations.tags.Tag;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.boot.CommandLineRunner;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.service.Parser;
import java.util.List;

@Slf4j
@Tag(name = "Lab2", description = "Lab 2 description")
@RestController
@RequestMapping("/rest/lab-2")
@RequiredArgsConstructor
public class CController implements CommandLineRunner {

    private final Parser parser;


    @Operation(description = "")
    @PostMapping(value = "/ss")
    public ResponseEntity<String> create(
    ) {
        return ResponseEntity.ok().body("");
    }

    @Override
    public void run(String... args) {
        Tree tree = parser.parser("((abc)*|(cde)*)*");
        Tree ssnf = ssnf(tree);
        log.info(ssnf.toString());
    }

    public Tree ssnf(Tree tree) {
        switch (tree.getType()) {
            case SYMBOL -> {
                return tree;
            }
            case OR -> {
                return new Tree(Tree.Type.OR, List.of(
                        ssnf(tree.getChildren().get(0)),
                        ssnf(tree.getChildren().get(1))
                ));
            }
            case CONCAT -> {
                return new Tree(Tree.Type.CONCAT, List.of(
                        ssnf(tree.getChildren().get(0)),
                        ssnf(tree.getChildren().get(1))
                ));
            }
            case ASTERISK -> {
                return new Tree(Tree.Type.ASTERISK, List.of(
                        ss(tree.getChildren().get(0))
                ));
            }
            case GROUP -> {
                return new Tree(Tree.Type.GROUP, List.of(
                        ssnf(tree.getChildren().get(0))
                ));
            }
            default -> throw new RuntimeException();
        }
    }

    public Tree ss(Tree tree) {
        switch (tree.getType()) {
            case SYMBOL -> {
                return tree;
            }
            case OR -> {
                return new Tree(Tree.Type.OR, List.of(
                        ss(tree.getChildren().get(0)),
                        ss(tree.getChildren().get(1))
                ));
            }
            case CONCAT -> {
                return new Tree(Tree.Type.CONCAT, List.of(
                        ssnf(tree.getChildren().get(0)),
                        ssnf(tree.getChildren().get(1))
                ));
            }
            case ASTERISK -> {
                return ss(tree.getChildren().get(0));
            }
            case GROUP -> {
                return new Tree(Tree.Type.GROUP, List.of(
                        ss(tree.getChildren().get(0))
                ));
            }
            default -> throw new RuntimeException();
        }
    }
}