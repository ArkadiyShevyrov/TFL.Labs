package ru.bmstu.iu9.tfl_lab_1_null;

import lombok.experimental.UtilityClass;
import lombok.extern.slf4j.Slf4j;
import ru.bmstu.iu9.tfl_lab_1_null.model.*;
import ru.bmstu.iu9.tfl_lab_lib_smt.TermUtils;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.SMT2;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.basic.*;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.part.Assert;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.part.DeclareConstant;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.part.DefineConstant;

import java.util.*;

import static ru.bmstu.iu9.tfl_lab_lib_smt.model.part.DeclareConstant.Type.INT;

@UtilityClass
@Slf4j
public class DominoSolve {

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


    private Set<Character> getAlphabet(List<Domino> dominoes) {
        Set<Character> alphabet = new HashSet<>();
        for (Domino domino : dominoes) {
            alphabet.addAll(charArrayToList(domino.getUp().toCharArray()));
            alphabet.addAll(charArrayToList(domino.getDown().toCharArray()));
        }
        return alphabet;
    }

    private List<Character> charArrayToList(char[] charArray) {
        List<Character> charList = new ArrayList<>();
        for (char c : charArray) {
            charList.add(c);
        }
        return charList;
    }

    public static SMT2 createSMT2FromDomino(List<Domino> dominoes) {
        log.info(Arrays.deepToString(dominoes.toArray()));
        Set<Character> alphabet = getAlphabet(dominoes);

        List<DeclareConstant> declareConstants = new ArrayList<>();
        List<DefineConstant> defineConstants = new ArrayList<>();
        List<Assert> asserts = new ArrayList<>();

        List<DominoIndex> dominoIndexes =
                initDominoIndixes(dominoes);
        List<CountDomino> countDominoes =
                initCountDominos(dominoIndexes, declareConstants, asserts);

        List<CountPairDominoToRight> countPairDominoToRights =
                initCountPairDominoToRights(dominoIndexes, declareConstants, asserts);
        List<IsLastDomino> isLastDominoes =
                initIsLastDominos(dominoIndexes, declareConstants, asserts);
        associateCountDominoToRightsWithLastDomino
                (dominoIndexes, countPairDominoToRights, countDominoes, isLastDominoes, asserts);

        List<CountPairDominoToLeft> countPairDominoToLefts =
                initCountPairDominoToLefts(dominoIndexes, declareConstants, asserts);
        List<IsFirstDomino> isFirstDominoes =
                initIsFirstDominos(dominoIndexes, declareConstants, asserts);
        associateCountDominoToLeftsWithFirstDomino
                (dominoIndexes, countPairDominoToLefts, countDominoes, isFirstDominoes, asserts);

        associateCountDominoToRightWithCountDominoToLeft
                (dominoIndexes, countPairDominoToRights, countPairDominoToLefts, asserts);

        List<CountLetter> countLetters = initCountLetters(dominoIndexes, alphabet, defineConstants);

        // Количество пар букв внутри доминошки
        for (int i = 0; i < dominoes.size(); i++) {
            for (Character letter1 : alphabet) {
                for (Character letter2 : alphabet) {
                    ValueTerm up = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i);
                    ValueTerm down = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i);
                    defineConstants.add(new DefineConstant(up, DefineConstant.Type.INT,
                            String.valueOf(cnt(
                                    dominoes.get(i).getUp(),
                                    String.valueOf(letter1) + letter2))
                    ));
                    defineConstants.add(new DefineConstant(down, DefineConstant.Type.INT,
                            String.valueOf(cnt(
                                    dominoes.get(i).getDown(),
                                    String.valueOf(letter1) + letter2))
                    ));
                }
            }
        }

        // Пары букв на стыках доминошек+
        for (int i = 0; i < dominoes.size(); i++) {
            for (int j = 0; j < dominoes.size(); j++) {
                for (Character letter1 : alphabet) {
                    for (Character letter2 : alphabet) {
                        ValueTerm up = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i + "d" + j);
                        ValueTerm down = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i + "d" + j);

                        String lastOfAo = String.valueOf(dominoes.get(i).getUp().charAt(dominoes.get(i).getUp().length() - 1));
                        String lastOfA1 = String.valueOf(dominoes.get(i).getDown().charAt(dominoes.get(i).getDown().length() - 1));
                        String firstOfA0 = String.valueOf(dominoes.get(j).getUp().charAt(0));
                        String firstOfA1 = String.valueOf(dominoes.get(j).getDown().charAt(0));

                        defineConstants.add(new DefineConstant(up, DefineConstant.Type.INT,
                                String.valueOf(cnt(
                                        lastOfAo + firstOfA0,
                                        String.valueOf(letter1) + letter2))));
                        defineConstants.add(new DefineConstant(down, DefineConstant.Type.INT,
                                String.valueOf(cnt(
                                        lastOfA1 + firstOfA1,
                                        String.valueOf(letter1) + letter2))));
                    }
                }
            }
        }

        // Пары букв на стыках доминошек-
        for (int i = 0; i < dominoes.size(); i++) {
            for (int j = 0; j < dominoes.size(); j++) {
                for (Character letter1 : alphabet) {
                    for (Character letter2 : alphabet) {
                        ValueTerm up = new ValueTerm("PPu_" + letter1 + letter2 + "d" + i + "d" + j);
                        ValueTerm down = new ValueTerm("PPd_" + letter1 + letter2 + "d" + i + "d" + j);

                        String lastOfAo = String.valueOf(dominoes.get(j).getUp().charAt(dominoes.get(j).getUp().length() - 1));
                        String lastOfA1 = String.valueOf(dominoes.get(j).getDown().charAt(dominoes.get(j).getDown().length() - 1));
                        String firstOfA0 = String.valueOf(dominoes.get(i).getUp().charAt(0));
                        String firstOfA1 = String.valueOf(dominoes.get(i).getDown().charAt(0));

                        defineConstants.add(new DefineConstant(up, DefineConstant.Type.INT,
                                String.valueOf(cnt(
                                        lastOfAo + firstOfA0,
                                        String.valueOf(letter1) + letter2))
                        ));
                        defineConstants.add(new DefineConstant(down, DefineConstant.Type.INT,
                                String.valueOf(cnt(
                                        lastOfA1 + firstOfA1,
                                        String.valueOf(letter1) + letter2))
                        ));
                    }
                }
            }
        }

        // Сравним количество букв
        for (Character letter : alphabet) {
            List<Term> sumUp = new ArrayList<>();
            List<Term> sumDown = new ArrayList<>();
            for (int i = 0; i < dominoes.size(); i++) {
                Term md = new ValueTerm("!CountDomino_" + i);
                Term lu = new ValueTerm("CountLetter_up_" + i + "_" + letter);
                Term ld = new ValueTerm("CountLetter_down_" + i + "_" + letter);

                sumUp.add(new MultTerm(md, lu));
                sumDown.add(new MultTerm(md, ld));
            }

            asserts.add(new Assert(
                    new EqualTerm(
                            new SumTerm(sumUp),
                            new SumTerm(sumDown)
                    )
            ));
        }

        // Сравним количество пар букв+
        for (Character letter1 : alphabet) {
            for (Character letter2 : alphabet) {
                List<Term> sumUp = new ArrayList<>();
                List<Term> sumDown = new ArrayList<>();
                for (int i = 0; i < dominoes.size(); i++) {
                    Term md = new ValueTerm("!CountDomino_" + i);
                    Term pu = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i);
                    Term pd = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i);
                    sumUp.add(new MultTerm(md, pu));
                    sumDown.add(new MultTerm(md, pd));
                    for (int j = 0; j < dominoes.size(); j++) {
                        Term mdd = new ValueTerm("!CountPairDominoToRight_" + i + "_" + j);
                        Term pud = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i + "d" + j);
                        Term pdd = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i + "d" + j);
                        sumUp.add(new MultTerm(mdd, pud));
                        sumDown.add(new MultTerm(mdd, pdd));
                    }
                }

                asserts.add(new Assert(
                        new EqualTerm(
                                new SumTerm(sumUp),
                                new SumTerm(sumDown)
                        )
                ));
            }
        }

        // Сравним количество пар букв-
        for (Character letter1 : alphabet) {
            for (Character letter2 : alphabet) {
                List<Term> sumUp = new ArrayList<>();
                List<Term> sumDown = new ArrayList<>();
                for (int i = 0; i < dominoes.size(); i++) {
                    Term md = new ValueTerm("!CountDomino_" + i);
                    Term pu = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i);
                    Term pd = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i);
                    sumUp.add(new MultTerm(md, pu));
                    sumDown.add(new MultTerm(md, pd));
                    for (int j = 0; j < dominoes.size(); j++) {
                        Term mdd = new ValueTerm("!CountPairDominoToLeft_" + i + "_" + j);
                        Term pud = new ValueTerm("PPu_" + letter1 + letter2 + "d" + i + "d" + j);
                        Term pdd = new ValueTerm("PPd_" + letter1 + letter2 + "d" + i + "d" + j);
                        sumUp.add(new MultTerm(mdd, pud));
                        sumDown.add(new MultTerm(mdd, pdd));
                    }
                }

                asserts.add(new Assert(
                        new EqualTerm(
                                new SumTerm(sumUp),
                                new SumTerm(sumDown)
                        )
                ));
            }
        }


        return new SMT2(declareConstants, defineConstants, asserts);
    }

    private static List<CountLetter> initCountLetters(List<DominoIndex> dominoIndexes, Set<Character> alphabet, List<DefineConstant> defineConstants) {
        // Количество букв
        List<CountLetter> countLetters = new ArrayList<>();
        for (DominoIndex dominoIndex : dominoIndexes) {
            for (Character letter : alphabet) {
                countLetters.add(new CountLetter(
                        CountLetter.Type.UP, dominoIndex, letter));
                countLetters.add(new CountLetter(
                        CountLetter.Type.DOWN, dominoIndex, letter));
            }
        }

        for (CountLetter countLetter : countLetters) {
            String value = switch (countLetter.getType()) {
                case UP -> String.valueOf(cnt(
                        countLetter.getDominoIndex().getDomino().getUp(),
                        countLetter.getLetter().toString()));
                case DOWN -> String.valueOf(cnt(
                        countLetter.getDominoIndex().getDomino().getDown(),
                        countLetter.getLetter().toString()));
            };
            defineConstants.add(
                    new DefineConstant(
                            countLetter.toTerm(),
                            DefineConstant.Type.INT,
                            value));
        }
        return countLetters;
    }

    private static void associateCountDominoToRightWithCountDominoToLeft(List<DominoIndex> dominoIndexes, List<CountPairDominoToRight> countPairDominoToRights, List<CountPairDominoToLeft> countPairDominoToLefts, List<Assert> asserts) {
        for (DominoIndex left : dominoIndexes) {
            for (DominoIndex right : dominoIndexes) {
                CountPairDominoToRight countPairDominoToRight =
                        CountPairDominoToRight.getAllByDominoTwoIndex(countPairDominoToRights, left, right);
                CountPairDominoToLeft countPairDominoToLeft =
                        CountPairDominoToLeft.getAllByDominoTwoIndex(countPairDominoToLefts, right, left);
                assert countPairDominoToRight != null;
                assert countPairDominoToLeft != null;
                asserts.add(
                        new Assert(
                                new EqualTerm(
                                        countPairDominoToRight.toTerm(),
                                        countPairDominoToLeft.toTerm())));
            }
        }
    }

    private static void associateCountDominoToLeftsWithFirstDomino(List<DominoIndex> dominoIndexes, List<CountPairDominoToLeft> countPairDominoToLefts, List<CountDomino> countDominoes, List<IsFirstDomino> isFirstDominoes, List<Assert> asserts) {
        for (DominoIndex dominoIndex : dominoIndexes) {
            List<CountPairDominoToLeft> pairsToLeft =
                    CountPairDominoToLeft.getAllByDominoIndexLeft
                            (countPairDominoToLefts, dominoIndex);
            CountDomino countDomino = CountDomino.getByDominoIndex(countDominoes, dominoIndex);
            IsFirstDomino isFirstDomino = IsFirstDomino.getByDominoIndex(isFirstDominoes, dominoIndex);
            assert countDomino != null;
            assert isFirstDomino != null;
            asserts.add(
                    new Assert(
                            new EqualTerm(
                                    new SumTerm(TermUtils.toListTerm(pairsToLeft)),
                                    new MinusTerm(
                                            countDomino.toTerm(),
                                            isFirstDomino.toTerm()
                                    )
                            )
                    )
            );
        }
    }

    private static void associateCountDominoToRightsWithLastDomino(List<DominoIndex> dominoIndexes, List<CountPairDominoToRight> countPairDominoToRights, List<CountDomino> countDominoes, List<IsLastDomino> isLastDominoes, List<Assert> asserts) {
        for (DominoIndex dominoIndex : dominoIndexes) {
            List<CountPairDominoToRight> pairsToRight =
                    CountPairDominoToRight.getAllByDominoIndexLeft
                            (countPairDominoToRights, dominoIndex);
            CountDomino countDomino = CountDomino.getByDominoIndex(countDominoes, dominoIndex);
            IsLastDomino isLastDomino = IsLastDomino.getByDominoIndex(isLastDominoes, dominoIndex);
            assert countDomino != null;
            assert isLastDomino != null;
            asserts.add(
                    new Assert(
                            new EqualTerm(
                                    new SumTerm(TermUtils.toListTerm(pairsToRight)),
                                    new MinusTerm(
                                            countDomino.toTerm(),
                                            isLastDomino.toTerm()
                                    )
                            )
                    )
            );
        }
    }

    private static List<IsFirstDomino> initIsFirstDominos(List<DominoIndex> dominoIndexes, List<DeclareConstant> declareConstants, List<Assert> asserts) {
        List<IsFirstDomino> isFirstDominoes = new ArrayList<>();
        for (DominoIndex dominoIndex : dominoIndexes) {
            isFirstDominoes.add(new IsFirstDomino(dominoIndex));
        }

        for (IsFirstDomino isFirstDomino : isFirstDominoes) {
            declareConstants.add(
                    new DeclareConstant(isFirstDomino.toTerm(), INT));
        }

        for (IsFirstDomino isFirstDomino : isFirstDominoes) {
            asserts.add(
                    new Assert(
                            new GreaterEqualTerm(
                                    isFirstDomino.toTerm(),
                                    new ValueTerm("0"))));
        }

        asserts.add(
                new Assert(
                        new EqualTerm(
                                new SumTerm(TermUtils.toListTerm(isFirstDominoes)),
                                new ValueTerm("1"))));
        return isFirstDominoes;
    }

    private static List<CountPairDominoToLeft> initCountPairDominoToLefts(List<DominoIndex> dominoIndexes, List<DeclareConstant> declareConstants, List<Assert> asserts) {
        List<CountPairDominoToLeft> countPairDominoToLefts = new ArrayList<>();
        for (DominoIndex left : dominoIndexes) {
            for (DominoIndex right : dominoIndexes) {
                countPairDominoToLefts.add(
                        new CountPairDominoToLeft(left, right));
            }
        }

        for (CountPairDominoToLeft countPairDominoToLeft : countPairDominoToLefts) {
            declareConstants.add(
                    new DeclareConstant(
                            countPairDominoToLeft.toTerm(), INT));
        }

        for (CountPairDominoToLeft countPairDominoToLeft : countPairDominoToLefts) {
            asserts.add(
                    new Assert(
                            new GreaterEqualTerm(
                                    countPairDominoToLeft.toTerm(),
                                    new ValueTerm("0"))));
        }
        return countPairDominoToLefts;
    }

    private static List<IsLastDomino> initIsLastDominos(List<DominoIndex> dominoIndexes, List<DeclareConstant> declareConstants, List<Assert> asserts) {
        List<IsLastDomino> isLastDominoes = new ArrayList<>();
        for (DominoIndex dominoIndex : dominoIndexes) {
            isLastDominoes.add(new IsLastDomino(dominoIndex));
        }

        for (IsLastDomino isLastDomino : isLastDominoes) {
            declareConstants.add(
                    new DeclareConstant(isLastDomino.toTerm(), INT));
        }

        for (IsLastDomino isLastDomino : isLastDominoes) {
            asserts.add(
                    new Assert(
                            new GreaterEqualTerm(
                                    isLastDomino.toTerm(),
                                    new ValueTerm("0"))));
        }

        asserts.add(
                new Assert(
                        new EqualTerm(
                                new SumTerm(TermUtils.toListTerm(isLastDominoes)),
                                new ValueTerm("1"))));
        return isLastDominoes;
    }

    private static List<DominoIndex> initDominoIndixes(List<Domino> dominoes) {
        List<DominoIndex> dominoIndexes = new ArrayList<>();
        int index = 0;
        for (Domino domino : dominoes) {
            dominoIndexes.add(new DominoIndex(domino, index++));
        }
        return dominoIndexes;
    }

    private static List<CountPairDominoToRight> initCountPairDominoToRights(List<DominoIndex> dominoIndexes, List<DeclareConstant> declareConstants, List<Assert> asserts) {
        List<CountPairDominoToRight> countPairDominoToRights = new ArrayList<>();
        for (DominoIndex left : dominoIndexes) {
            for (DominoIndex right : dominoIndexes) {
                countPairDominoToRights.add(
                        new CountPairDominoToRight(left, right));
            }
        }

        for (CountPairDominoToRight countPairDominoToRight : countPairDominoToRights) {
            declareConstants.add(
                    new DeclareConstant(
                            countPairDominoToRight.toTerm(), INT));
        }

        for (CountPairDominoToRight countPairDominoToRight : countPairDominoToRights) {
            asserts.add(
                    new Assert(
                            new GreaterEqualTerm(
                                    countPairDominoToRight.toTerm(),
                                    new ValueTerm("0"))));
        }
        return countPairDominoToRights;
    }

    private static List<CountDomino> initCountDominos(List<DominoIndex> dominoIndexes, List<DeclareConstant> declareConstants, List<Assert> asserts) {
        List<CountDomino> countDominoes = new ArrayList<>();
        for (DominoIndex dominoIndex : dominoIndexes) {
            countDominoes.add(
                    new CountDomino(dominoIndex));
        }

        for (CountDomino countDomino : countDominoes) {
            declareConstants.add(
                    new DeclareConstant(countDomino.toTerm(), INT));
        }

        for (CountDomino countDomino : countDominoes) {
            asserts.add(
                    new Assert(
                            new GreaterEqualTerm(
                                    countDomino.toTerm(),
                                    new ValueTerm("0"))));
        }
        return countDominoes;
    }
}
