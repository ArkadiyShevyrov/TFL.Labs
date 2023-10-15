package ru.bmstu.iu9.tfl_lab_2;

import lombok.extern.slf4j.Slf4j;

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
    public static Tree normalizeAssociativity(Tree root) {
        if (root == null) {
            return null;
        }

        if (root.value == '|') {
            while (root.left != null && root.left.value == '|') {
                // Применяем ассоциативность
                Tree leftChild = root.left;
                root.left = leftChild.right;
                leftChild.right = root;
                root = leftChild;
            }
        }

        // Рекурсивно применяем ассоциативность к левому и правому поддеревьям
        root.left = normalizeAssociativity(root.left);
        root.right = normalizeAssociativity(root.right);

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
        root.left = new Tree('|');
        root.left.left = new Tree('|');
        root.left.left.left = new Tree('a');
        root.left.left.right = new Tree('b');
        root.left.right = new Tree('c');
        root.right = new Tree('d');

        System.out.println("Исходное дерево:");
        printTree(root, "", true);

        // Нормализация по ассоциативности
        root = normalizeAssociativity(root);

        System.out.println("\nНормализованное дерево:");
        printTree(root, "", true);
    }
}