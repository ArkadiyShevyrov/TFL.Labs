package ru.bmstu.iu9.tfl_lab_2.utils;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_2.model.Tree;

@UtilityClass
public class DSTR {
    public Tree dstrTree(Tree root) {
        if (root == null) {
            return null;
        }
        root = dstrl(root);
        root = dstrr(root);
        root.setLeft(dstrTree(root.getLeft()));
        root.setRight(dstrTree(root.getRight()));
        return root;
    }

    private static Tree dstrr(Tree root) {
        if (root.getType() == Tree.Type.CONCAT &&
                root.getRight().getType() == Tree.Type.OR) {
            root = new Tree(
                    Tree.Type.OR,
                    new Tree(
                            Tree.Type.CONCAT,
                            root.getLeft(),
                            root.getRight().getLeft()),
                    new Tree(
                            Tree.Type.CONCAT,
                            root.getLeft(),
                            root.getRight().getRight()));
        }
        return root;
    }

    private static Tree dstrl(Tree root) {
        if (root.getType() == Tree.Type.CONCAT &&
                root.getLeft().getType() == Tree.Type.OR) {
            root = new Tree(
                    Tree.Type.OR,
                    new Tree(
                            Tree.Type.CONCAT,
                            root.getLeft().getLeft(),
                            root.getRight()),
                    new Tree(
                            Tree.Type.CONCAT,
                            root.getLeft().getRight(),
                            root.getRight()));
        }
        return root;
    }
}
