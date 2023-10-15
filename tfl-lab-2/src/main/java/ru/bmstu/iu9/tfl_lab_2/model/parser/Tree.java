package ru.bmstu.iu9.tfl_lab_2.model.parser;

import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import java.io.Serializable;

@Slf4j
@Getter
@Setter
@AllArgsConstructor
public class Tree implements Serializable {
    private final Type type;
    private String value;

    private Tree left;
    private Tree right;

    public Tree(Type type) {
        this.type = type;
    }

    public Tree(Type type, Tree left) {
        this.type = type;
        this.left = left;
    }

    public Tree(Type type, Tree left, Tree right) {
        this.type = type;
        this.left = left;
        this.right = right;
    }

    public Tree(Type type, String value) {
        this.type = type;
        this.value = value;
    }

    public static String drawTree(Tree root) {
        return "\n" + printTree(root, "", false);
    }

    private static String printTree(Tree root, String prefix, boolean isLeft) {
        StringBuilder builder = new StringBuilder();
        if (root != null) {
            builder.append(prefix + (isLeft ? "├── " : "└── ") + root.getType() +
                    (root.getValue() != null ? " " + root.getValue() : "")).append("\n");
            String s1 = printTree(root.left, prefix + (isLeft ? "│   " : "    "), root.right != null);
            String s2 = printTree(root.right, prefix + (isLeft ? "│   " : "    "), false);
            builder.append(s1).append(s2);
        }
        return builder.toString();
    }

    @Override
    public String toString() {
        switch (type) {
            case OR -> {
                return "("+left + "|" + right +")";
            }
            case CONCAT -> {
                return left + "" + right;
            }
            case SYMBOL -> {
                return value;
            }
            case ASTERISK -> {
                return "(" + left + ")" + "*";
            }
            case GROUP -> {
                return "(" + left + ")";
            }
            default -> {
                return "";
            }

        }
    }

//    public static Tree applyDSTR(Tree root) {
//        switch (root.type) {
//            case SYMBOL -> {
//                return root;
//            }
//            case CONCAT -> {
//                // Применяем левое распределение (DSTRL)
//                Tree newLeft = new Tree(Type.CONCAT, applyDSTR(root.left), applyDSTR(root.right));
//                Tree newRight = applyDSTR(root.right);
//                return new Tree(Type.CONCAT, newLeft, newRight);
//            }
//            case OR -> {
//                // Применяем правое распределение (DSTRR)
//                Tree newLeft = applyDSTR(root.left);
//                Tree newRight = applyDSTR(root.right);
//                return new Tree(Type.OR, newLeft, newRight);
//            }
//            case ASTERISK -> {
//                // Применяем правое распределение (DSTRR)
//                Tree newChild = applyDSTR(root.left);
//                return new Tree(Type.ASTERISK, newChild);
//            }
//            default -> {
//                return null;
//            }
//        }
//    }

    public enum Type {
        OR,
        CONCAT,
        ASTERISK,
        SYMBOL,
        GROUP;
    }
}
