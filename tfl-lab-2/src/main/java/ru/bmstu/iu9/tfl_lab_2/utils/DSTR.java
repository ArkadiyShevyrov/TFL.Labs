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
//        root = dstrr(root);
        root.setLeft(dstrTree(root.getLeft()));
        root.setRight(dstrTree(root.getRight()));
//        root = dstrl(root);
//        root = dstrr(root);
        return root;
    }

    private static Tree dstrr(Tree root) {
        if (root.getType() == Tree.Type.OR &&
                root.getLeft().getType() == Tree.Type.CONCAT &&
                root.getRight().getType() == Tree.Type.CONCAT &&
                root.getLeft().getRight().toString().equals(root.getRight().getRight().toString())) {
            root = new Tree(
                    Tree.Type.CONCAT,
                    new Tree(
                            Tree.Type.OR,
                            root.getLeft().getLeft(),
                            root.getRight().getLeft()),
                    root.getLeft().getRight());
        }
        return root;
    }

    private static Tree dstrl(Tree root) {
        while (root.getType() == Tree.Type.OR &&
                root.getLeft().getType() == Tree.Type.CONCAT &&
                root.getRight().getType() == Tree.Type.OR &&
                root.getRight().getLeft().getType() == Tree.Type.CONCAT &&
                root.getLeft().getLeft().toString().equals(root.getRight().getLeft().getLeft().toString())) {
            root = new Tree(
                    Tree.Type.OR,
                    root.getRight().getRight(),
                    new Tree(
                            Tree.Type.CONCAT,
                            root.getLeft().getLeft(),
                            new Tree(
                                    Tree.Type.OR,
                                    root.getLeft().getRight(),
                                    root.getRight().getLeft().getRight())));
        }
        if (root.getType() == Tree.Type.OR &&
                root.getLeft().getType() == Tree.Type.CONCAT &&
                root.getRight().getType() == Tree.Type.CONCAT &&
                root.getLeft().getLeft().toString().equals(root.getRight().getLeft().toString())) {
            root = new Tree(
                    Tree.Type.CONCAT,
                    root.getLeft().getLeft(),
                    new Tree(
                            Tree.Type.OR,
                            root.getLeft().getRight(),
                            root.getRight().getRight())
            );
        }
        return root;
    }
}
