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
import java.util.ArrayList;
import java.util.Comparator;

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
        if (root.getType() == Tree.Type.CONCAT) {
            while (root.getLeft() != null && root.getLeft().getType() == Tree.Type.CONCAT) {
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

    public static Tree normalizeCommutativity(Tree root) {
        if (root == null) {
            return null;
        }

        if (root.getType() == Tree.Type.OR) {
            // Собираем все операнды в список
            ArrayList<Tree> operands = collectOperands(root);
            operands.sort(Comparator.comparing(Tree::toString));
            return createTreeFromSortedOperands(operands);
        }

        // Рекурсивно применяем коммутативность к левому и правому поддеревьям
        root.setLeft(normalizeCommutativity(root.getLeft()));
        root.setRight(normalizeCommutativity(root.getRight()));

        return root;
    }

    public static ArrayList<Tree> collectOperands(Tree root) {
        ArrayList<Tree> operands = new ArrayList<>();
        if (root == null) {
            return null;
        }

        if (root.getType() == Tree.Type.OR) {
            if (root.getLeft().getType() != Tree.Type.OR) {
                operands.add(root.getLeft());
            } else {
                operands.addAll(collectOperands(root.getLeft()));
            }
            if (root.getRight().getType() != Tree.Type.OR) {
                operands.add(root.getRight());
            } else {
                operands.addAll(collectOperands(root.getRight()));

            }
        }
        return operands;
    }

    public static Tree createTreeFromSortedOperands(ArrayList<Tree> operands) {
        if (operands.isEmpty()) {
            return null;
        }

        Tree root = new Tree(Tree.Type.OR, operands.get(0));
        Tree current = root;

        for (int i = 1; i < operands.size()-1; i++) {
            if (i == operands.size() - 2) {
                Tree temp = new Tree(Tree.Type.OR, operands.get(i), operands.get(i+1));
                current.setRight(temp);
                current = temp;
                continue;
            }
            Tree temp = new Tree(Tree.Type.OR, operands.get(i));
            current.setRight(temp);
            current = temp;
        }

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
        Tree tree = parser.parser("(((a|c|a|b|a)|b)*|((acd)e)*)*");
        log.info(Tree.drawTree(tree));
        log.info(tree.toString());
        Tree ssnfTree = ssnf(SerializationUtils.clone(tree));
        log.info(Tree.drawTree(ssnfTree));
        log.info(ssnfTree.toString());
        Tree associativityTree = normalizeAssociativity(SerializationUtils.clone(ssnfTree));
        log.info(Tree.drawTree(associativityTree));
        log.info(associativityTree.toString());
        Tree commutativityTree = normalizeCommutativity(SerializationUtils.clone(associativityTree));
        log.info(Tree.drawTree(commutativityTree));
        log.info(commutativityTree.toString());
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