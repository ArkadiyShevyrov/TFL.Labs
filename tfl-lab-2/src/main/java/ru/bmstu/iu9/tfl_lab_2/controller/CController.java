package ru.bmstu.iu9.tfl_lab_2.controller;

import io.swagger.v3.oas.annotations.Operation;
import io.swagger.v3.oas.annotations.tags.Tag;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.lang3.SerializationUtils;
import org.springframework.boot.CommandLineRunner;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.service.Parser;

@Slf4j
@Tag(name = "Lab2", description = "Lab 2 description")
@RestController
@RequestMapping("/rest/lab-2")
@RequiredArgsConstructor
public class CController implements CommandLineRunner {

    private final Parser parser;

    public static Tree normalizeAssociativity(Tree root) {
        if (root == null) {
            return null;
        }
        if (root.getType() == Tree.Type.OR) {
            while (root.getLeft() != null && root.getLeft().getType() == Tree.Type.OR) {
                Tree leftChild = root.getLeft();
                root.setLeft(leftChild.getRight());
                leftChild.setRight(root);
                root = leftChild;
            }
        }
        root.setLeft(normalizeAssociativity(root.getLeft()));
        root.setRight(normalizeAssociativity(root.getRight()));
        return root;
    }

    @Operation(description = "")
    @PostMapping(value = "/ss")
    public ResponseEntity<String> create(
    ) {
        return ResponseEntity.ok().body("");
    }

    @Override
    public void run(String... args) {
        Tree tree = parser.parser("((abc)*|(cde)*)*");
        Tree.drawTree(tree);
        Tree ssnfTree = ssnf(SerializationUtils.clone(tree));
        Tree.drawTree(ssnfTree);
        Tree normTree = normalizeAssociativity(SerializationUtils.clone(ssnfTree));
        Tree.drawTree(normTree);
    }

    public Tree ssnf(Tree tree) {
        switch (tree.getType()) {
            case SYMBOL -> {
                return tree;
            }
            case OR -> {
                return new Tree(Tree.Type.OR, ssnf(tree.getLeft()),
                        ssnf(tree.getRight()));
            }
            case CONCAT -> {
                return new Tree(Tree.Type.CONCAT, ssnf(tree.getLeft()), ssnf(tree.getRight()));
            }
            case ASTERISK -> {
                return new Tree(Tree.Type.ASTERISK, ss(tree.getLeft()));
            }
            case GROUP -> {
                return new Tree(Tree.Type.GROUP, ssnf(tree.getLeft()));
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
                return new Tree(Tree.Type.OR, ss(tree.getLeft()), ss(tree.getRight()));
            }
            case CONCAT -> {
                Tree treeChildLeft = tree.getLeft();
                Tree treeChildRight = tree.getRight();
                if (treeChildLeft.getType() == Tree.Type.ASTERISK
                        && treeChildRight.getType() == Tree.Type.ASTERISK) {
                    return new Tree(Tree.Type.OR, ss(tree.getLeft()), ss(tree.getRight()));
                }
                return new Tree(Tree.Type.CONCAT, ssnf(tree.getLeft()),
                        ssnf(tree.getRight()));
            }
            case ASTERISK -> {
                return ss(tree.getLeft());
            }
            case GROUP -> {
                return new Tree(Tree.Type.GROUP, ss(tree.getLeft()));
            }
            default -> throw new RuntimeException();
        }
    }
}