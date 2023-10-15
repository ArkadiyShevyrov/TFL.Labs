package ru.bmstu.iu9.tfl_lab_2.utils;

import java.util.regex.*;

public class RegexAlgebra {
    public static String applyDSTRL(String regex1, String regex2, String regex3) {
        String result = "(" + regex1 + regex3 + ")|(" + regex2 + regex3 + ")";
        return result;
    }

    public static String applyDSTRR(String regex1, String regex2, String regex3) {
        String result = "(" + regex1 + regex2 + ")|(" + regex1 + regex3 + ")";
        return result;
    }

    public static void main(String[] args) {
        String regexA = "ab";
        String regexB = "cd";
        String regexC = "e";

        String dstrlResult = applyDSTRL(regexA, regexB, regexC);
        System.out.println("DSTRL Result: " + dstrlResult);

        String dstrrResult = applyDSTRR(regexA, regexB, regexC);
        System.out.println("DSTRR Result: " + dstrrResult);
    }
}
