package ru.bmstu.iu9.tfl_lab_1_null;


import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

public class Main {

    static List<String> mySplit(char delimiter, String str) {
        List<String> result = new ArrayList<>();
        int start = 0;
        for (int i = 0; i < str.length(); i++) {
            if (str.charAt(i) == delimiter) {
                result.add(str.substring(start, i));
                start = i + 1;
            }
        }
        result.add(str.substring(start));
        return result;
    }

    static int cnt(String s, String p) {
        if (p.length() > s.length()) {
            return 0;
        }
        int count = 0;
        for (int i = 0; i <= s.length() - p.length(); i++) {
            if (s.startsWith(p, i)) {
                count++;
            }
        }
        return count;
    }

    static List<Character> charArrayToList(char[] charArray) {
        List<Character> charList = new ArrayList<>();
        for (char c : charArray) {
            charList.add(c);
        }
        return charList;
    }

    public static void main(String[] args) {
        try (BufferedReader br = new BufferedReader(new FileReader("D:\\iu9\\TFL.Labs\\tfl-lab-2-null\\src\\main\\resources\\input.txt"));
             PrintWriter outFile = new PrintWriter(new FileWriter("out.smt2"))) {

            List<List<String>> a = new ArrayList<>();
            String line;
            while ((line = br.readLine()) != null) {
                a.add(mySplit(',', line.substring(1, line.length() - 1)));
            }

            Set<Character> alphabet = new HashSet<>();
            for (List<String> pair : a) {
                alphabet.addAll(charArrayToList(pair.get(0).toCharArray()));
                alphabet.addAll(charArrayToList(pair.get(1).toCharArray()));
            }

            for (int i = 0; i < a.size(); i++) {
                outFile.println("(declare-const Md" + i + " Int)");
                outFile.println("(assert (>= Md" + i + " 0))");
            }

            outFile.println();

            for (int i = 0; i < a.size(); i++) {
                for (int j = 0; j < a.size(); j++) {
                    outFile.println("(declare-const Md" + i + "d" + j + " Int)");
                    outFile.println("(assert (>= Md" + i + "d" + j + " 0))");
                }
            }

            outFile.println();

            for (int i = 0; i < a.size(); i++) {
                outFile.println("(declare-const IsLast_d" + i + " Int)");
                outFile.println("(assert (>= IsLast_d" + i + " 0))");
            }

            Stream<String> stringStream = a.stream().map(pair -> "IsLast_d" + a.indexOf(pair));
            String sum_lasts = stringStream.reduce((s1, s2) -> s1 + " " + s2).orElse("");
            outFile.println("(assert (= (+ " + sum_lasts + ") 1))");

            outFile.println();

            for (int i = 0; i < a.size(); i++) {
                int finalI = i;
                String sum_d = a.stream().map(pair -> "Md" + finalI + "d" + a.indexOf(pair)).reduce((s1, s2) -> s1 + " " + s2).orElse("");
                outFile.println("(assert (= (+ " + sum_d + ") (- Md" + i + " IsLast_d" + i + ")))");
            }

            outFile.println();

            for (int i = 0; i < a.size(); i++) {
                for (char letter : alphabet) {
                    outFile.println("(declare-const Lu_" + letter + "d" + i + " Int)");
                    outFile.println("(assert (= Lu_" + letter + "d" + i + " " + cnt(a.get(i).get(0), String.valueOf(letter)) + "))");

                    outFile.println("(declare-const Ld_" + letter + "d" + i + " Int)");
                    outFile.println("(assert (= Ld_" + letter + "d" + i + " " + cnt(a.get(i).get(1), String.valueOf(letter)) + "))");
                }
            }

            outFile.println();

            for (int i = 0; i < a.size(); i++) {
                for (char letter1 : alphabet) {
                    for (char letter2 : alphabet) {
                        outFile.println("(declare-const Pu_" + letter1 + letter2 + "d" + i + " Int)");
                        outFile.println("(assert (= Pu_" + letter1 + letter2 + "d" + i + " " + cnt(a.get(i).get(0), String.valueOf(letter1) + letter2) + "))");

                        outFile.println("(declare-const Pd_" + letter1 + letter2 + "d" + i + " Int)");
                        outFile.println("(assert (= Pd_" + letter1 + letter2 + "d" + i + " " + cnt(a.get(i).get(1), String.valueOf(letter1) + letter2) + "))");
                    }
                }
            }

            outFile.println();

            for (int i = 0; i < a.size(); i++) {
                for (int j = 0; j < a.size(); j++) {
                    for (char letter1 : alphabet) {
                        for (char letter2 : alphabet) {
                            String lastOfA0 = String.valueOf(a.get(i).get(0).charAt(a.get(i).get(0).length() - 1));
                            String firstOfA1 = String.valueOf(a.get(j).get(1).charAt(0));

                            outFile.println("(declare-const Pu_" + letter1 + letter2 + "d" + i + "d" + j + " Int)");
                            outFile.println("(assert (= Pu_" + letter1 + letter2 + "d" + i + "d" + j + " " +
                                    cnt(lastOfA0 + firstOfA1, String.valueOf(letter1) + letter2) + "))");

                            outFile.println("(declare-const Pd_" + letter1 + letter2 + "d" + i + "d" + j + " Int)");
                            outFile.println("(assert (= Pd_" + letter1 + letter2 + "d" + i + "d" + j + " " +
                                    cnt(lastOfA0 + firstOfA1, String.valueOf(letter1) + letter2) + "))");
                        }
                    }
                }
            }

            outFile.println();

            for (char letter : alphabet) {
                String sum_u = a.stream().map(pair -> "(* Md" + a.indexOf(pair) + " Lu_" + letter + "d" + a.indexOf(pair) + ")").reduce((s1, s2) -> s1 + " " + s2).orElse("");
                String sum_d = a.stream().map(pair -> "(* Md" + a.indexOf(pair) + " Ld_" + letter + "d" + a.indexOf(pair) + ")").reduce((s1, s2) -> s1 + " " + s2).orElse("");
                outFile.println("(assert (= (+ " + sum_u + ") (+ " + sum_d + ")  ))");
            }

            outFile.println();

            for (char letter1 : alphabet) {
                for (char letter2 : alphabet) {
                    String r = "(assert (= (+ " +
                            a.stream().map(pair -> "(* Md" + a.indexOf(pair) + " Pu_" + letter1 + letter2 + "d" + a.indexOf(pair) + ")").reduce((s1, s2) -> s1 + " " + s2).orElse("") +
                            a.stream().flatMap(i -> a.stream().map(j -> "(* Md" + a.indexOf(i) + "d" + a.indexOf(j) + " Pu_" + letter1 + letter2 + "d" + a.indexOf(i) + "d" + a.indexOf(j) + ")")).reduce((s1, s2) -> s1 + " " + s2).orElse("") +
                            ") (+ " +
                            a.stream().map(pair -> "(* Md" + a.indexOf(pair) + " Pd_" + letter1 + letter2 + "d" + a.indexOf(pair) + ")").reduce((s1, s2) -> s1 + " " + s2).orElse("") +
                            a.stream().flatMap(i -> a.stream().map(j -> "(* Md" + a.indexOf(i) + "d" + a.indexOf(j) + " Pd_" + letter1 + letter2 + "d" + a.indexOf(i) + "d" + a.indexOf(j) + ")")).reduce((s1, s2) -> s1 + " " + s2).orElse("") +
                            ")))";
                    outFile.println(r);
                }
            }

            outFile.println("(check-sat)");

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}

