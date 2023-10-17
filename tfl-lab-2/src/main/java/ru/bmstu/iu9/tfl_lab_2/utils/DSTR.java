package ru.bmstu.iu9.tfl_lab_2.utils;

import lombok.experimental.UtilityClass;
import org.apache.commons.lang3.SerializationUtils;
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
        if (root.getType() == Tree.Type.OR &&
                root.getLeft().getType() == Tree.Type.CONCAT &&
                root.getRight().getType() == Tree.Type.CONCAT &&
                root.getLeft().getRight().toString().equals(root.getRight().getRight().toString())) {
            root = new Tree(
                    Tree.Type.CONCAT,
                    normalOr(new Tree(
                            Tree.Type.OR,
                            root.getLeft().getLeft(),
                            root.getRight().getLeft())),
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
            root = normalOr(new Tree(
                    Tree.Type.OR,
                    root.getRight().getRight(),
                    new Tree(
                            Tree.Type.CONCAT,
                            root.getLeft().getLeft(),
                            normalOr(new Tree(
                                    Tree.Type.OR,
                                    root.getLeft().getRight(),
                                    root.getRight().getLeft().getRight())))));
        }
        if (root.getType() == Tree.Type.OR &&
                root.getLeft().getType() == Tree.Type.CONCAT &&
                root.getRight().getType() == Tree.Type.CONCAT &&
                root.getLeft().getLeft().toString().equals(root.getRight().getLeft().toString())) {
            root = new Tree(
                    Tree.Type.CONCAT,
                    root.getLeft().getLeft(),
                    normalOr(new Tree(
                            Tree.Type.OR,
                            root.getLeft().getRight(),
                            root.getRight().getRight()))
            );
        }
        root = ACI.normalizeCommutativity(SerializationUtils.clone(root));
        return root;
    }

    private Tree normalOr(Tree tree) {
        if (tree.getLeft().getType() == Tree.Type.OR &&
                tree.getRight().getType() != Tree.Type.OR) {
            Tree temp = tree.getLeft();
            tree.setLeft(tree.getRight());
            tree.setRight(temp);
        }
        return tree;
    }
}
