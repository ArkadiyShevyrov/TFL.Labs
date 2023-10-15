package ru.bmstu.iu9.tfl_lab_2.utils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

class TreeNode {
    String value;
    List<TreeNode> children;

    public TreeNode(String value) {
        this.value = value;
        this.children = new ArrayList<>();
    }

    public void addChild(TreeNode child) {
        children.add(child);
    }

    public void sortChildren() {
        Collections.sort(children, (a, b) -> a.value.compareTo(b.value));
        for (TreeNode child : children) {
            child.sortChildren();
        }
    }

    public void printTree(int level) {
        for (int i = 0; i < level; i++) {
            System.out.print("    ");
        }
        System.out.println("├── " + value);
        for (TreeNode child : children) {
            child.printTree(level + 1);
        }
    }
}

public class Main {
    public static void main(String[] args) {
        TreeNode root = new TreeNode("ASTERISK");
        TreeNode or1 = new TreeNode("OR");
        TreeNode symbolC = new TreeNode("SYMBOL c");
        TreeNode or2 = new TreeNode("OR");
        TreeNode symbolA = new TreeNode("SYMBOL a");
        TreeNode or3 = new TreeNode("OR");
        TreeNode symbolB = new TreeNode("SYMBOL b");
        TreeNode concat1 = new TreeNode("CONCAT");
        TreeNode symbolA2 = new TreeNode("SYMBOL a");
        TreeNode concat2 = new TreeNode("CONCAT");
        TreeNode symbolC2 = new TreeNode("SYMBOL c");
        TreeNode concat3 = new TreeNode("CONCAT");
        TreeNode symbolD = new TreeNode("SYMBOL d");
        TreeNode symbolE = new TreeNode("SYMBOL e");

        root.addChild(or1);
        or1.addChild(symbolC);
        or1.addChild(or2);
        or2.addChild(symbolA);
        or2.addChild(or3);
        or3.addChild(symbolB);
        or3.addChild(concat1);
        concat1.addChild(symbolA2);
        concat1.addChild(concat2);
        concat2.addChild(symbolC2);
        concat2.addChild(concat3);
        concat3.addChild(symbolD);
        concat3.addChild(symbolE);

        root.sortChildren();
        root.printTree(0);
    }
}
