package ru.bmstu.iu9.tfl_lab_1_null;

import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import io.swagger.v3.oas.annotations.Operation;
import io.swagger.v3.oas.annotations.Parameter;
import io.swagger.v3.oas.annotations.tags.Tag;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import ru.bmstu.iu9.tfl_lab_1_null.model.rest.Domino;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.SMT2;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.interfaces.Term;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.part.Assert;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.part.DeclareConst;
import ru.bmstu.iu9.tfl_lab_1_null.model.smt.term.basic.*;

import java.util.*;

@Slf4j
@Tag(name = "Lab1-null", description = "Lab 1-null description")
@RestController
@RequestMapping("/rest/lab-1-null")
@RequiredArgsConstructor
public class ControllerLab2Null {


    public static void main(String[] args) {
        ControllerLab2Null controllerLab2Null = new ControllerLab2Null();
        controllerLab2Null.convert("""
                (a,ab)
                (bab,a)
                (a,ba)
                """);
    }

    @Operation(description = "Решение проблем соответствия Поста")
    @PostMapping(value = "/solutionsProblemsPostCompliance")
    public ResponseEntity<String> convert(
            @Parameter(description = "problem")
            @RequestBody String problem
    ) {
        log.info(problem);
        List<Domino> dominoes = createDomino(problem);
        log.info(Arrays.deepToString(dominoes.toArray()));
        Set<Character> alphabet = getAlphabet(dominoes);
        log.info(Arrays.deepToString(alphabet.toArray()));

        List<DeclareConst> declareConstants = new ArrayList<>();
        List<Assert> asserts = new ArrayList<>();

        // Количество вхождений доминошек
        List<Term> Md = new ArrayList<>();
        for (int i = 0; i < dominoes.size(); i++) {
            Md.add(new ValueTerm("Md" + i));
        }
        for (Term term : Md) {
            declareConstants.add(new DeclareConst(term));
            asserts.add(new Assert(
                    new GreaterEqualTerm(
                            term,
                            new ValueTerm("0"))));
        }


        // Количество вхождений пар доминошек
        List<Term> Mdd = new ArrayList<>();
        for (int i = 0; i < dominoes.size(); i++) {
            for (int j = 0; j < dominoes.size(); j++) {
                Mdd.add(new ValueTerm("Md" + i + "d" + j));
            }
        }
        for (Term term : Mdd) {
            declareConstants.add(new DeclareConst(term));
            asserts.add(new Assert(
                    new GreaterEqualTerm(
                            term,
                            new ValueTerm("0"))));
        }

        //   -- определим последнюю доминошку
        List<Term> isLastD = new ArrayList<>();
        for (int i = 0; i < dominoes.size(); i++) {
            isLastD.add(new ValueTerm("IsLast_d" + i));
        }
        for (Term valueTerm : isLastD) {
            declareConstants.add(new DeclareConst(valueTerm));
            asserts.add(new Assert(
                    new GreaterEqualTerm(
                            valueTerm,
                            new ValueTerm("0"))));
        }
        asserts.add(new Assert(
                new EqualTerm(
                        new SumTerm(isLastD),
                        new ValueTerm("1"))));

        // Связываем количество доминошек с последним
        for (int i = 0; i < dominoes.size(); i++) {
            List<Term> sumDD = new ArrayList<>();
            for (int j = 0; j < dominoes.size(); j++) {
                sumDD.add(Mdd.get(i * dominoes.size() + j));
            }
            asserts.add(new Assert(
                    new EqualTerm(
                            new SumTerm(sumDD),
                            new MinusTerm(
                                    Md.get(i),
                                    isLastD.get(i)))));
        }

//         Количество вхождений пар доминошек
        List<Term> MMdd = new ArrayList<>();
        for (int i = 0; i < dominoes.size(); i++) {
            for (int j = 0; j < dominoes.size(); j++) {
                MMdd.add(new ValueTerm("MMd" + i + "d" + j));
            }
        }
        for (Term term : MMdd) {
            declareConstants.add(new DeclareConst(term));
            asserts.add(new Assert(
                    new GreaterEqualTerm(
                            term,
                            new ValueTerm("0"))));
        }

        //   -- определим первую доминошку
        List<Term> isFirstD = new ArrayList<>();
        for (int i = 0; i < dominoes.size(); i++) {
            isFirstD.add(new ValueTerm("IsFirst_d" + i));
        }
        for (Term valueTerm : isFirstD) {
            declareConstants.add(new DeclareConst(valueTerm));
            asserts.add(new Assert(
                    new GreaterEqualTerm(
                            valueTerm,
                            new ValueTerm("0"))));
        }
        asserts.add(new Assert(
                new EqualTerm(
                        new SumTerm(isFirstD),
                        new ValueTerm("1"))));


        // Связываем количество доминошек с первым
        for (int i = 0; i < dominoes.size(); i++) {
            List<Term> sumDD = new ArrayList<>();
            for (int j = 0; j < dominoes.size(); j++) {
                sumDD.add(MMdd.get(i * dominoes.size() + j));
            }
            asserts.add(new Assert(
                    new EqualTerm(
                            new SumTerm(sumDD),
                            new MinusTerm(
                                    Md.get(i),
                                    isFirstD.get(i)))));
        }

        // Количество букв
        List<Term> LetterUpDom = new ArrayList<>();
        List<Term> LetterDownDom = new ArrayList<>();
        for (int i = 0; i < dominoes.size(); i++) {
            for (Character letter : alphabet) {
                ValueTerm up = new ValueTerm("Lu_" + letter + "d" + i);
                ValueTerm down = new ValueTerm("Ld_" + letter + "d" + i);

                declareConstants.add(new DeclareConst(up));
                declareConstants.add(new DeclareConst(down));

                asserts.add(new Assert(
                        new EqualTerm(
                                up,
                                new ValueTerm(
                                        String.valueOf(
                                                cnt(dominoes.get(i).getUp(),
                                                        letter.toString()))))));
                asserts.add(new Assert(
                        new EqualTerm(
                                down,
                                new ValueTerm(
                                        String.valueOf(
                                                cnt(dominoes.get(i).getDown(),
                                                        letter.toString()))))));
            }
        }

        // Количество пар букв внутри доминошки
        for (int i = 0; i < dominoes.size(); i++) {
            for (Character letter1 : alphabet) {
                for (Character letter2 : alphabet) {
                    ValueTerm up = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i);
                    ValueTerm down = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i);

                    declareConstants.add(new DeclareConst(up));
                    declareConstants.add(new DeclareConst(down));

                    asserts.add(new Assert(
                            new EqualTerm(
                                    up,
                                    new ValueTerm(
                                            String.valueOf(
                                                    cnt(
                                                            dominoes.get(i).getUp(),
                                                            String.valueOf(letter1) + letter2))))));
                    asserts.add(new Assert(
                            new EqualTerm(
                                    down,
                                    new ValueTerm(
                                            String.valueOf(
                                                    cnt(
                                                            dominoes.get(i).getDown(),
                                                            String.valueOf(letter1) + letter2))))));
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

                        declareConstants.add(new DeclareConst(up));
                        declareConstants.add(new DeclareConst(down));

                        asserts.add(new Assert(
                                new EqualTerm(
                                        up,
                                        new ValueTerm(
                                                String.valueOf(
                                                        cnt(
                                                                lastOfAo + firstOfA0,
                                                                String.valueOf(letter1) + letter2))))));
                        asserts.add(new Assert(
                                new EqualTerm(
                                        down,
                                        new ValueTerm(
                                                String.valueOf(
                                                        cnt(
                                                                lastOfA1 + firstOfA1,
                                                                String.valueOf(letter1) + letter2))))));
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

                        declareConstants.add(new DeclareConst(up));
                        declareConstants.add(new DeclareConst(down));

                        asserts.add(new Assert(
                                new EqualTerm(
                                        up,
                                        new ValueTerm(
                                                String.valueOf(
                                                        cnt(
                                                                lastOfAo + firstOfA0,
                                                                String.valueOf(letter1) + letter2))))));
                        asserts.add(new Assert(
                                new EqualTerm(
                                        down,
                                        new ValueTerm(
                                                String.valueOf(
                                                        cnt(
                                                                lastOfA1 + firstOfA1,
                                                                String.valueOf(letter1) + letter2))))));
                    }
                }
            }
        }

        // Сравним количество букв
        for (Character letter : alphabet) {
            List<Term> sumUp = new ArrayList<>();
            List<Term> sumDown = new ArrayList<>();
            for (int i = 0; i < dominoes.size(); i++) {
                Term md = new ValueTerm("Md" + i);
                Term lu = new ValueTerm("Lu_" + letter + "d" + i);
                Term ld = new ValueTerm("Ld_" + letter + "d" + i);

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
                    Term md = new ValueTerm("Md" + i);
                    Term pu = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i);
                    Term pd = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i);
                    sumUp.add(new MultTerm(md, pu));
                    sumDown.add(new MultTerm(md, pd));
                    for (int j = 0; j < dominoes.size(); j++) {
                        Term mdd = new ValueTerm("Md" + i + "d" + j);
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
                    Term md = new ValueTerm("Md" + i);
                    Term pu = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i);
                    Term pd = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i);
                    sumUp.add(new MultTerm(md, pu));
                    sumDown.add(new MultTerm(md, pd));
                    for (int j = 0; j < dominoes.size(); j++) {
                        Term mdd = new ValueTerm("MMd" + i + "d" + j);
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

        for (int i = 0; i < dominoes.size(); i++) {
            for (int j = 0; j < dominoes.size(); j++) {
                Term mdd = new ValueTerm("Md" + i + "d" + j);
                Term mmdd = new ValueTerm("MMd" + j + "d" + i);

                asserts.add(new Assert(
                        new EqualTerm(
                                mdd,
                                mmdd)));
            }
        }


        SMT2 smt2 = new SMT2(declareConstants, asserts);

        log.info("\n" + smt2);
        String body = smtGen(smt2.toString());
        log.info(body);

        return ResponseEntity.ok().body(body);
    }

    public String smtGen(String string) {
        try (Context context = new Context()) {
            Solver solver = context.mkSimpleSolver();
            solver.fromString(string);
            Status check = solver.check();
            Model model = solver.getModel();
            return solver.check().toString();
        }
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

    private List<Domino> createDomino(String problem) {
        List<Domino> dominoes = new ArrayList<>();
        List<String> dominoStrings = List.of(problem.split("\n"));
        for (String domineString : dominoStrings) {
            dominoes.add(new Domino(domineString));
        }
        return dominoes;
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
}
