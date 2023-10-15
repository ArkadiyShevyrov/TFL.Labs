package ru.bmstu.iu9.tfl_lab_2;

import lombok.extern.slf4j.Slf4j;
import java.util.ArrayList;
import java.util.Collections;

class Tree {
    char value;
    Tree left;
    Tree right;

    public Tree(char value) {
        this.value = value;
        this.left = null;
        this.right = null;
    }

    // Дополнительные методы, если необходимо
}
@Slf4j
public class RegexNormalization {
    public static Tree normalizeCommutativity(Tree root) {
        if (root == null) {
            return null;
        }

        if (root.value == '|') {
            // Собираем все операнды в список
            ArrayList<Character> operands = new ArrayList<>();
            collectOperands(root, operands);

            // Сортируем операнды по алфавиту
            Collections.sort(operands);

            // Создаем новое дерево с отсортированными операндами
            Tree sortedTree = createTreeFromSortedOperands(operands);

            return sortedTree;
        }

        // Рекурсивно применяем коммутативность к левому и правому поддеревьям
        root.left = normalizeCommutativity(root.left);
        root.right = normalizeCommutativity(root.right);

        return root;
    }

    public static void collectOperands(Tree root, ArrayList<Character> operands) {
        if (root == null) {
            return;
        }

        if (Character.isLetter(root.value)) {
            operands.add(root.value);
        }

        collectOperands(root.left, operands);
        collectOperands(root.right, operands);
    }

    public static Tree createTreeFromSortedOperands(ArrayList<Character> operands) {
        if (operands.isEmpty()) {
            return null;
        }

        Tree root = new Tree(operands.get(0));
        Tree current = root;

        for (int i = 1; i < operands.size(); i++) {
            current.right = new Tree(operands.get(i));
            current = current.right;
        }

        return root;
    }

    public static void printTree(Tree root, String prefix, boolean isLeft) {
        if (root != null) {
            log.info(prefix + (isLeft ? "├── " : "└── ") + root.value);
            printTree(root.left, prefix + (isLeft ? "│   " : "    "), true);
            printTree(root.right, prefix + (isLeft ? "│   " : "    "), false);
        }
    }

    public static void main(String[] args) {
        // Пример дерева регулярного выражения
        Tree root = new Tree('|');
        root.left = new Tree('c');
        Tree rightSubtree = new Tree('|');
        rightSubtree.left = new Tree('a');
        rightSubtree.right = new Tree('|');
        rightSubtree.right.left = new Tree('d');
        rightSubtree.right.right = new Tree('b');
        root.right = rightSubtree;

        System.out.println("Исходное дерево:");
        printTree(root, "", false);

        // Нормализация по коммутативности
        root = normalizeCommutativity(root);

        System.out.println("\nНормализованное дерево:");
        printTree(root, "", false);
    }
}