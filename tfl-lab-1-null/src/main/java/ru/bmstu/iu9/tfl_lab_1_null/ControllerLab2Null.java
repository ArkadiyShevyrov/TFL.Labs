package ru.bmstu.iu9.tfl_lab_1_null;

import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
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
                (a,a)
                (b,b)
                (d,c)
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

        // Связываем количество доминошек и пар доминошек
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

        // Пары букв на стыках доминошек
        for (int i = 0; i < dominoes.size(); i++) {
            for (int j = 0; j < dominoes.size(); j++) {
                for (Character letter1 : alphabet) {
                    for (Character letter2 : alphabet) {
                        ValueTerm up = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i + "d" + j);
                        ValueTerm down = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i+ "d" + j);

                        String lastOfAo = String.valueOf(dominoes.get(i).getUp().charAt(dominoes.get(i).getUp().length() - 1));
                        String firstOfA1 = String.valueOf(dominoes.get(j).getDown().charAt(0));

                        declareConstants.add(new DeclareConst(up));
                        declareConstants.add(new DeclareConst(down));

                        asserts.add(new Assert(
                                new EqualTerm(
                                        up,
                                        new ValueTerm(
                                                String.valueOf(
                                                        cnt(
                                                                lastOfAo + firstOfA1,
                                                                String.valueOf(letter1) + letter2))))));
                        asserts.add(new Assert(
                                new EqualTerm(
                                        down,
                                        new ValueTerm(
                                                String.valueOf(
                                                        cnt(
                                                                lastOfAo + firstOfA1,
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

        // Сравним количество пар букв
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
                        Term pud = new ValueTerm("Pu_" + letter1 + letter2 + "d" + i+ "d" + j);
                        Term pdd = new ValueTerm("Pd_" + letter1 + letter2 + "d" + i+ "d" + j);
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


        SMT2 smt2 = new SMT2(declareConstants, asserts);

//        log.info("\n" +smt2);
//        String body = smtGen(smt2.toString());
//        log.info(body);
        String body = smtGen("""
                (declare-const Md0 Int)
                (assert (>= Md0 0))
                (declare-const Md1 Int)
                (assert (>= Md1 0))
                (declare-const Md2 Int)
                (assert (>= Md2 0))
                                
                (declare-const Md0d0 Int)
                (assert (>= Md0d0 0))
                (declare-const Md0d1 Int)
                (assert (>= Md0d1 0))
                (declare-const Md0d2 Int)
                (assert (>= Md0d2 0))
                (declare-const Md1d0 Int)
                (assert (>= Md1d0 0))
                (declare-const Md1d1 Int)
                (assert (>= Md1d1 0))
                (declare-const Md1d2 Int)
                (assert (>= Md1d2 0))
                (declare-const Md2d0 Int)
                (assert (>= Md2d0 0))
                (declare-const Md2d1 Int)
                (assert (>= Md2d1 0))
                (declare-const Md2d2 Int)
                (assert (>= Md2d2 0))
                                
                (declare-const IsLast_d0 Int)
                (assert (>= IsLast_d0 0))
                (declare-const IsLast_d1 Int)
                (assert (>= IsLast_d1 0))
                (declare-const IsLast_d2 Int)
                (assert (>= IsLast_d2 0))
                (assert (= (+ IsLast_d0 IsLast_d1 IsLast_d2) 1))
                                
                (assert(=(+ Md0d0 Md0d1 Md0d2)(- Md0 IsLast_d0)))
                (assert(=(+ Md1d0 Md1d1 Md1d2)(- Md1 IsLast_d1)))
                (assert(=(+ Md2d0 Md2d1 Md2d2)(- Md2 IsLast_d2)))
                                
                (declare-const Lu_ad0 Int)
                (assert (= Lu_ad0 1))
                (declare-const Ld_ad0 Int)
                (assert (= Ld_ad0 1))
                (declare-const Lu_bd0 Int)
                (assert (= Lu_bd0 0))
                (declare-const Ld_bd0 Int)
                (assert (= Ld_bd0 0))
                (declare-const Lu_dd0 Int)
                (assert (= Lu_dd0 0))
                (declare-const Ld_dd0 Int)
                (assert (= Ld_dd0 0))
                (declare-const Lu_cd0 Int)
                (assert (= Lu_cd0 0))
                (declare-const Ld_cd0 Int)
                (assert (= Ld_cd0 0))
                (declare-const Lu_ad1 Int)
                (assert (= Lu_ad1 0))
                (declare-const Ld_ad1 Int)
                (assert (= Ld_ad1 0))
                (declare-const Lu_bd1 Int)
                (assert (= Lu_bd1 1))
                (declare-const Ld_bd1 Int)
                (assert (= Ld_bd1 1))
                (declare-const Lu_dd1 Int)
                (assert (= Lu_dd1 0))
                (declare-const Ld_dd1 Int)
                (assert (= Ld_dd1 0))
                (declare-const Lu_cd1 Int)
                (assert (= Lu_cd1 0))
                (declare-const Ld_cd1 Int)
                (assert (= Ld_cd1 0))
                (declare-const Lu_ad2 Int)
                (assert (= Lu_ad2 0))
                (declare-const Ld_ad2 Int)
                (assert (= Ld_ad2 0))
                (declare-const Lu_bd2 Int)
                (assert (= Lu_bd2 0))
                (declare-const Ld_bd2 Int)
                (assert (= Ld_bd2 0))
                (declare-const Lu_dd2 Int)
                (assert (= Lu_dd2 1))
                (declare-const Ld_dd2 Int)
                (assert (= Ld_dd2 0))
                (declare-const Lu_cd2 Int)
                (assert (= Lu_cd2 0))
                (declare-const Ld_cd2 Int)
                (assert (= Ld_cd2 1))
                                
                (declare-const Pu_aad0 Int)
                (assert (= Pu_aad0 0))
                (declare-const Pd_aad0 Int)
                (assert (= Pd_aad0 0))
                (declare-const Pu_abd0 Int)
                (assert (= Pu_abd0 0))
                (declare-const Pd_abd0 Int)
                (assert (= Pd_abd0 0))
                (declare-const Pu_add0 Int)
                (assert (= Pu_add0 0))
                (declare-const Pd_add0 Int)
                (assert (= Pd_add0 0))
                (declare-const Pu_acd0 Int)
                (assert (= Pu_acd0 0))
                (declare-const Pd_acd0 Int)
                (assert (= Pd_acd0 0))
                (declare-const Pu_bad0 Int)
                (assert (= Pu_bad0 0))
                (declare-const Pd_bad0 Int)
                (assert (= Pd_bad0 0))
                (declare-const Pu_bbd0 Int)
                (assert (= Pu_bbd0 0))
                (declare-const Pd_bbd0 Int)
                (assert (= Pd_bbd0 0))
                (declare-const Pu_bdd0 Int)
                (assert (= Pu_bdd0 0))
                (declare-const Pd_bdd0 Int)
                (assert (= Pd_bdd0 0))
                (declare-const Pu_bcd0 Int)
                (assert (= Pu_bcd0 0))
                (declare-const Pd_bcd0 Int)
                (assert (= Pd_bcd0 0))
                (declare-const Pu_dad0 Int)
                (assert (= Pu_dad0 0))
                (declare-const Pd_dad0 Int)
                (assert (= Pd_dad0 0))
                (declare-const Pu_dbd0 Int)
                (assert (= Pu_dbd0 0))
                (declare-const Pd_dbd0 Int)
                (assert (= Pd_dbd0 0))
                (declare-const Pu_ddd0 Int)
                (assert (= Pu_ddd0 0))
                (declare-const Pd_ddd0 Int)
                (assert (= Pd_ddd0 0))
                (declare-const Pu_dcd0 Int)
                (assert (= Pu_dcd0 0))
                (declare-const Pd_dcd0 Int)
                (assert (= Pd_dcd0 0))
                (declare-const Pu_cad0 Int)
                (assert (= Pu_cad0 0))
                (declare-const Pd_cad0 Int)
                (assert (= Pd_cad0 0))
                (declare-const Pu_cbd0 Int)
                (assert (= Pu_cbd0 0))
                (declare-const Pd_cbd0 Int)
                (assert (= Pd_cbd0 0))
                (declare-const Pu_cdd0 Int)
                (assert (= Pu_cdd0 0))
                (declare-const Pd_cdd0 Int)
                (assert (= Pd_cdd0 0))
                (declare-const Pu_ccd0 Int)
                (assert (= Pu_ccd0 0))
                (declare-const Pd_ccd0 Int)
                (assert (= Pd_ccd0 0))
                (declare-const Pu_aad1 Int)
                (assert (= Pu_aad1 0))
                (declare-const Pd_aad1 Int)
                (assert (= Pd_aad1 0))
                (declare-const Pu_abd1 Int)
                (assert (= Pu_abd1 0))
                (declare-const Pd_abd1 Int)
                (assert (= Pd_abd1 0))
                (declare-const Pu_add1 Int)
                (assert (= Pu_add1 0))
                (declare-const Pd_add1 Int)
                (assert (= Pd_add1 0))
                (declare-const Pu_acd1 Int)
                (assert (= Pu_acd1 0))
                (declare-const Pd_acd1 Int)
                (assert (= Pd_acd1 0))
                (declare-const Pu_bad1 Int)
                (assert (= Pu_bad1 0))
                (declare-const Pd_bad1 Int)
                (assert (= Pd_bad1 0))
                (declare-const Pu_bbd1 Int)
                (assert (= Pu_bbd1 0))
                (declare-const Pd_bbd1 Int)
                (assert (= Pd_bbd1 0))
                (declare-const Pu_bdd1 Int)
                (assert (= Pu_bdd1 0))
                (declare-const Pd_bdd1 Int)
                (assert (= Pd_bdd1 0))
                (declare-const Pu_bcd1 Int)
                (assert (= Pu_bcd1 0))
                (declare-const Pd_bcd1 Int)
                (assert (= Pd_bcd1 0))
                (declare-const Pu_dad1 Int)
                (assert (= Pu_dad1 0))
                (declare-const Pd_dad1 Int)
                (assert (= Pd_dad1 0))
                (declare-const Pu_dbd1 Int)
                (assert (= Pu_dbd1 0))
                (declare-const Pd_dbd1 Int)
                (assert (= Pd_dbd1 0))
                (declare-const Pu_ddd1 Int)
                (assert (= Pu_ddd1 0))
                (declare-const Pd_ddd1 Int)
                (assert (= Pd_ddd1 0))
                (declare-const Pu_dcd1 Int)
                (assert (= Pu_dcd1 0))
                (declare-const Pd_dcd1 Int)
                (assert (= Pd_dcd1 0))
                (declare-const Pu_cad1 Int)
                (assert (= Pu_cad1 0))
                (declare-const Pd_cad1 Int)
                (assert (= Pd_cad1 0))
                (declare-const Pu_cbd1 Int)
                (assert (= Pu_cbd1 0))
                (declare-const Pd_cbd1 Int)
                (assert (= Pd_cbd1 0))
                (declare-const Pu_cdd1 Int)
                (assert (= Pu_cdd1 0))
                (declare-const Pd_cdd1 Int)
                (assert (= Pd_cdd1 0))
                (declare-const Pu_ccd1 Int)
                (assert (= Pu_ccd1 0))
                (declare-const Pd_ccd1 Int)
                (assert (= Pd_ccd1 0))
                (declare-const Pu_aad2 Int)
                (assert (= Pu_aad2 0))
                (declare-const Pd_aad2 Int)
                (assert (= Pd_aad2 0))
                (declare-const Pu_abd2 Int)
                (assert (= Pu_abd2 0))
                (declare-const Pd_abd2 Int)
                (assert (= Pd_abd2 0))
                (declare-const Pu_add2 Int)
                (assert (= Pu_add2 0))
                (declare-const Pd_add2 Int)
                (assert (= Pd_add2 0))
                (declare-const Pu_acd2 Int)
                (assert (= Pu_acd2 0))
                (declare-const Pd_acd2 Int)
                (assert (= Pd_acd2 0))
                (declare-const Pu_bad2 Int)
                (assert (= Pu_bad2 0))
                (declare-const Pd_bad2 Int)
                (assert (= Pd_bad2 0))
                (declare-const Pu_bbd2 Int)
                (assert (= Pu_bbd2 0))
                (declare-const Pd_bbd2 Int)
                (assert (= Pd_bbd2 0))
                (declare-const Pu_bdd2 Int)
                (assert (= Pu_bdd2 0))
                (declare-const Pd_bdd2 Int)
                (assert (= Pd_bdd2 0))
                (declare-const Pu_bcd2 Int)
                (assert (= Pu_bcd2 0))
                (declare-const Pd_bcd2 Int)
                (assert (= Pd_bcd2 0))
                (declare-const Pu_dad2 Int)
                (assert (= Pu_dad2 0))
                (declare-const Pd_dad2 Int)
                (assert (= Pd_dad2 0))
                (declare-const Pu_dbd2 Int)
                (assert (= Pu_dbd2 0))
                (declare-const Pd_dbd2 Int)
                (assert (= Pd_dbd2 0))
                (declare-const Pu_ddd2 Int)
                (assert (= Pu_ddd2 0))
                (declare-const Pd_ddd2 Int)
                (assert (= Pd_ddd2 0))
                (declare-const Pu_dcd2 Int)
                (assert (= Pu_dcd2 0))
                (declare-const Pd_dcd2 Int)
                (assert (= Pd_dcd2 0))
                (declare-const Pu_cad2 Int)
                (assert (= Pu_cad2 0))
                (declare-const Pd_cad2 Int)
                (assert (= Pd_cad2 0))
                (declare-const Pu_cbd2 Int)
                (assert (= Pu_cbd2 0))
                (declare-const Pd_cbd2 Int)
                (assert (= Pd_cbd2 0))
                (declare-const Pu_cdd2 Int)
                (assert (= Pu_cdd2 0))
                (declare-const Pd_cdd2 Int)
                (assert (= Pd_cdd2 0))
                (declare-const Pu_ccd2 Int)
                (assert (= Pu_ccd2 0))
                (declare-const Pd_ccd2 Int)
                (assert (= Pd_ccd2 0))
                                
                (declare-const Pu_aad0d0 Int)
                (assert (= Pu_aad0d0 1))
                (declare-const Pd_aad0d0 Int)
                (assert (= Pd_aad0d0 1))
                (declare-const Pu_abd0d0 Int)
                (assert (= Pu_abd0d0 0))
                (declare-const Pd_abd0d0 Int)
                (assert (= Pd_abd0d0 0))
                (declare-const Pu_add0d0 Int)
                (assert (= Pu_add0d0 0))
                (declare-const Pd_add0d0 Int)
                (assert (= Pd_add0d0 0))
                (declare-const Pu_acd0d0 Int)
                (assert (= Pu_acd0d0 0))
                (declare-const Pd_acd0d0 Int)
                (assert (= Pd_acd0d0 0))
                (declare-const Pu_bad0d0 Int)
                (assert (= Pu_bad0d0 0))
                (declare-const Pd_bad0d0 Int)
                (assert (= Pd_bad0d0 0))
                (declare-const Pu_bbd0d0 Int)
                (assert (= Pu_bbd0d0 0))
                (declare-const Pd_bbd0d0 Int)
                (assert (= Pd_bbd0d0 0))
                (declare-const Pu_bdd0d0 Int)
                (assert (= Pu_bdd0d0 0))
                (declare-const Pd_bdd0d0 Int)
                (assert (= Pd_bdd0d0 0))
                (declare-const Pu_bcd0d0 Int)
                (assert (= Pu_bcd0d0 0))
                (declare-const Pd_bcd0d0 Int)
                (assert (= Pd_bcd0d0 0))
                (declare-const Pu_dad0d0 Int)
                (assert (= Pu_dad0d0 0))
                (declare-const Pd_dad0d0 Int)
                (assert (= Pd_dad0d0 0))
                (declare-const Pu_dbd0d0 Int)
                (assert (= Pu_dbd0d0 0))
                (declare-const Pd_dbd0d0 Int)
                (assert (= Pd_dbd0d0 0))
                (declare-const Pu_ddd0d0 Int)
                (assert (= Pu_ddd0d0 0))
                (declare-const Pd_ddd0d0 Int)
                (assert (= Pd_ddd0d0 0))
                (declare-const Pu_dcd0d0 Int)
                (assert (= Pu_dcd0d0 0))
                (declare-const Pd_dcd0d0 Int)
                (assert (= Pd_dcd0d0 0))
                (declare-const Pu_cad0d0 Int)
                (assert (= Pu_cad0d0 0))
                (declare-const Pd_cad0d0 Int)
                (assert (= Pd_cad0d0 0))
                (declare-const Pu_cbd0d0 Int)
                (assert (= Pu_cbd0d0 0))
                (declare-const Pd_cbd0d0 Int)
                (assert (= Pd_cbd0d0 0))
                (declare-const Pu_cdd0d0 Int)
                (assert (= Pu_cdd0d0 0))
                (declare-const Pd_cdd0d0 Int)
                (assert (= Pd_cdd0d0 0))
                (declare-const Pu_ccd0d0 Int)
                (assert (= Pu_ccd0d0 0))
                (declare-const Pd_ccd0d0 Int)
                (assert (= Pd_ccd0d0 0))
                (declare-const Pu_aad0d1 Int)
                (assert (= Pu_aad0d1 0))
                (declare-const Pd_aad0d1 Int)
                (assert (= Pd_aad0d1 0))
                (declare-const Pu_abd0d1 Int)
                (assert (= Pu_abd0d1 1))
                (declare-const Pd_abd0d1 Int)
                (assert (= Pd_abd0d1 1))
                (declare-const Pu_add0d1 Int)
                (assert (= Pu_add0d1 0))
                (declare-const Pd_add0d1 Int)
                (assert (= Pd_add0d1 0))
                (declare-const Pu_acd0d1 Int)
                (assert (= Pu_acd0d1 0))
                (declare-const Pd_acd0d1 Int)
                (assert (= Pd_acd0d1 0))
                (declare-const Pu_bad0d1 Int)
                (assert (= Pu_bad0d1 0))
                (declare-const Pd_bad0d1 Int)
                (assert (= Pd_bad0d1 0))
                (declare-const Pu_bbd0d1 Int)
                (assert (= Pu_bbd0d1 0))
                (declare-const Pd_bbd0d1 Int)
                (assert (= Pd_bbd0d1 0))
                (declare-const Pu_bdd0d1 Int)
                (assert (= Pu_bdd0d1 0))
                (declare-const Pd_bdd0d1 Int)
                (assert (= Pd_bdd0d1 0))
                (declare-const Pu_bcd0d1 Int)
                (assert (= Pu_bcd0d1 0))
                (declare-const Pd_bcd0d1 Int)
                (assert (= Pd_bcd0d1 0))
                (declare-const Pu_dad0d1 Int)
                (assert (= Pu_dad0d1 0))
                (declare-const Pd_dad0d1 Int)
                (assert (= Pd_dad0d1 0))
                (declare-const Pu_dbd0d1 Int)
                (assert (= Pu_dbd0d1 0))
                (declare-const Pd_dbd0d1 Int)
                (assert (= Pd_dbd0d1 0))
                (declare-const Pu_ddd0d1 Int)
                (assert (= Pu_ddd0d1 0))
                (declare-const Pd_ddd0d1 Int)
                (assert (= Pd_ddd0d1 0))
                (declare-const Pu_dcd0d1 Int)
                (assert (= Pu_dcd0d1 0))
                (declare-const Pd_dcd0d1 Int)
                (assert (= Pd_dcd0d1 0))
                (declare-const Pu_cad0d1 Int)
                (assert (= Pu_cad0d1 0))
                (declare-const Pd_cad0d1 Int)
                (assert (= Pd_cad0d1 0))
                (declare-const Pu_cbd0d1 Int)
                (assert (= Pu_cbd0d1 0))
                (declare-const Pd_cbd0d1 Int)
                (assert (= Pd_cbd0d1 0))
                (declare-const Pu_cdd0d1 Int)
                (assert (= Pu_cdd0d1 0))
                (declare-const Pd_cdd0d1 Int)
                (assert (= Pd_cdd0d1 0))
                (declare-const Pu_ccd0d1 Int)
                (assert (= Pu_ccd0d1 0))
                (declare-const Pd_ccd0d1 Int)
                (assert (= Pd_ccd0d1 0))
                (declare-const Pu_aad0d2 Int)
                (assert (= Pu_aad0d2 0))
                (declare-const Pd_aad0d2 Int)
                (assert (= Pd_aad0d2 0))
                (declare-const Pu_abd0d2 Int)
                (assert (= Pu_abd0d2 0))
                (declare-const Pd_abd0d2 Int)
                (assert (= Pd_abd0d2 0))
                (declare-const Pu_add0d2 Int)
                (assert (= Pu_add0d2 1))
                (declare-const Pd_add0d2 Int)
                (assert (= Pd_add0d2 0))
                (declare-const Pu_acd0d2 Int)
                (assert (= Pu_acd0d2 0))
                (declare-const Pd_acd0d2 Int)
                (assert (= Pd_acd0d2 1))
                (declare-const Pu_bad0d2 Int)
                (assert (= Pu_bad0d2 0))
                (declare-const Pd_bad0d2 Int)
                (assert (= Pd_bad0d2 0))
                (declare-const Pu_bbd0d2 Int)
                (assert (= Pu_bbd0d2 0))
                (declare-const Pd_bbd0d2 Int)
                (assert (= Pd_bbd0d2 0))
                (declare-const Pu_bdd0d2 Int)
                (assert (= Pu_bdd0d2 0))
                (declare-const Pd_bdd0d2 Int)
                (assert (= Pd_bdd0d2 0))
                (declare-const Pu_bcd0d2 Int)
                (assert (= Pu_bcd0d2 0))
                (declare-const Pd_bcd0d2 Int)
                (assert (= Pd_bcd0d2 0))
                (declare-const Pu_dad0d2 Int)
                (assert (= Pu_dad0d2 0))
                (declare-const Pd_dad0d2 Int)
                (assert (= Pd_dad0d2 0))
                (declare-const Pu_dbd0d2 Int)
                (assert (= Pu_dbd0d2 0))
                (declare-const Pd_dbd0d2 Int)
                (assert (= Pd_dbd0d2 0))
                (declare-const Pu_ddd0d2 Int)
                (assert (= Pu_ddd0d2 0))
                (declare-const Pd_ddd0d2 Int)
                (assert (= Pd_ddd0d2 0))
                (declare-const Pu_dcd0d2 Int)
                (assert (= Pu_dcd0d2 0))
                (declare-const Pd_dcd0d2 Int)
                (assert (= Pd_dcd0d2 0))
                (declare-const Pu_cad0d2 Int)
                (assert (= Pu_cad0d2 0))
                (declare-const Pd_cad0d2 Int)
                (assert (= Pd_cad0d2 0))
                (declare-const Pu_cbd0d2 Int)
                (assert (= Pu_cbd0d2 0))
                (declare-const Pd_cbd0d2 Int)
                (assert (= Pd_cbd0d2 0))
                (declare-const Pu_cdd0d2 Int)
                (assert (= Pu_cdd0d2 0))
                (declare-const Pd_cdd0d2 Int)
                (assert (= Pd_cdd0d2 0))
                (declare-const Pu_ccd0d2 Int)
                (assert (= Pu_ccd0d2 0))
                (declare-const Pd_ccd0d2 Int)
                (assert (= Pd_ccd0d2 0))
                (declare-const Pu_aad1d0 Int)
                (assert (= Pu_aad1d0 0))
                (declare-const Pd_aad1d0 Int)
                (assert (= Pd_aad1d0 0))
                (declare-const Pu_abd1d0 Int)
                (assert (= Pu_abd1d0 0))
                (declare-const Pd_abd1d0 Int)
                (assert (= Pd_abd1d0 0))
                (declare-const Pu_add1d0 Int)
                (assert (= Pu_add1d0 0))
                (declare-const Pd_add1d0 Int)
                (assert (= Pd_add1d0 0))
                (declare-const Pu_acd1d0 Int)
                (assert (= Pu_acd1d0 0))
                (declare-const Pd_acd1d0 Int)
                (assert (= Pd_acd1d0 0))
                (declare-const Pu_bad1d0 Int)
                (assert (= Pu_bad1d0 1))
                (declare-const Pd_bad1d0 Int)
                (assert (= Pd_bad1d0 1))
                (declare-const Pu_bbd1d0 Int)
                (assert (= Pu_bbd1d0 0))
                (declare-const Pd_bbd1d0 Int)
                (assert (= Pd_bbd1d0 0))
                (declare-const Pu_bdd1d0 Int)
                (assert (= Pu_bdd1d0 0))
                (declare-const Pd_bdd1d0 Int)
                (assert (= Pd_bdd1d0 0))
                (declare-const Pu_bcd1d0 Int)
                (assert (= Pu_bcd1d0 0))
                (declare-const Pd_bcd1d0 Int)
                (assert (= Pd_bcd1d0 0))
                (declare-const Pu_dad1d0 Int)
                (assert (= Pu_dad1d0 0))
                (declare-const Pd_dad1d0 Int)
                (assert (= Pd_dad1d0 0))
                (declare-const Pu_dbd1d0 Int)
                (assert (= Pu_dbd1d0 0))
                (declare-const Pd_dbd1d0 Int)
                (assert (= Pd_dbd1d0 0))
                (declare-const Pu_ddd1d0 Int)
                (assert (= Pu_ddd1d0 0))
                (declare-const Pd_ddd1d0 Int)
                (assert (= Pd_ddd1d0 0))
                (declare-const Pu_dcd1d0 Int)
                (assert (= Pu_dcd1d0 0))
                (declare-const Pd_dcd1d0 Int)
                (assert (= Pd_dcd1d0 0))
                (declare-const Pu_cad1d0 Int)
                (assert (= Pu_cad1d0 0))
                (declare-const Pd_cad1d0 Int)
                (assert (= Pd_cad1d0 0))
                (declare-const Pu_cbd1d0 Int)
                (assert (= Pu_cbd1d0 0))
                (declare-const Pd_cbd1d0 Int)
                (assert (= Pd_cbd1d0 0))
                (declare-const Pu_cdd1d0 Int)
                (assert (= Pu_cdd1d0 0))
                (declare-const Pd_cdd1d0 Int)
                (assert (= Pd_cdd1d0 0))
                (declare-const Pu_ccd1d0 Int)
                (assert (= Pu_ccd1d0 0))
                (declare-const Pd_ccd1d0 Int)
                (assert (= Pd_ccd1d0 0))
                (declare-const Pu_aad1d1 Int)
                (assert (= Pu_aad1d1 0))
                (declare-const Pd_aad1d1 Int)
                (assert (= Pd_aad1d1 0))
                (declare-const Pu_abd1d1 Int)
                (assert (= Pu_abd1d1 0))
                (declare-const Pd_abd1d1 Int)
                (assert (= Pd_abd1d1 0))
                (declare-const Pu_add1d1 Int)
                (assert (= Pu_add1d1 0))
                (declare-const Pd_add1d1 Int)
                (assert (= Pd_add1d1 0))
                (declare-const Pu_acd1d1 Int)
                (assert (= Pu_acd1d1 0))
                (declare-const Pd_acd1d1 Int)
                (assert (= Pd_acd1d1 0))
                (declare-const Pu_bad1d1 Int)
                (assert (= Pu_bad1d1 0))
                (declare-const Pd_bad1d1 Int)
                (assert (= Pd_bad1d1 0))
                (declare-const Pu_bbd1d1 Int)
                (assert (= Pu_bbd1d1 1))
                (declare-const Pd_bbd1d1 Int)
                (assert (= Pd_bbd1d1 1))
                (declare-const Pu_bdd1d1 Int)
                (assert (= Pu_bdd1d1 0))
                (declare-const Pd_bdd1d1 Int)
                (assert (= Pd_bdd1d1 0))
                (declare-const Pu_bcd1d1 Int)
                (assert (= Pu_bcd1d1 0))
                (declare-const Pd_bcd1d1 Int)
                (assert (= Pd_bcd1d1 0))
                (declare-const Pu_dad1d1 Int)
                (assert (= Pu_dad1d1 0))
                (declare-const Pd_dad1d1 Int)
                (assert (= Pd_dad1d1 0))
                (declare-const Pu_dbd1d1 Int)
                (assert (= Pu_dbd1d1 0))
                (declare-const Pd_dbd1d1 Int)
                (assert (= Pd_dbd1d1 0))
                (declare-const Pu_ddd1d1 Int)
                (assert (= Pu_ddd1d1 0))
                (declare-const Pd_ddd1d1 Int)
                (assert (= Pd_ddd1d1 0))
                (declare-const Pu_dcd1d1 Int)
                (assert (= Pu_dcd1d1 0))
                (declare-const Pd_dcd1d1 Int)
                (assert (= Pd_dcd1d1 0))
                (declare-const Pu_cad1d1 Int)
                (assert (= Pu_cad1d1 0))
                (declare-const Pd_cad1d1 Int)
                (assert (= Pd_cad1d1 0))
                (declare-const Pu_cbd1d1 Int)
                (assert (= Pu_cbd1d1 0))
                (declare-const Pd_cbd1d1 Int)
                (assert (= Pd_cbd1d1 0))
                (declare-const Pu_cdd1d1 Int)
                (assert (= Pu_cdd1d1 0))
                (declare-const Pd_cdd1d1 Int)
                (assert (= Pd_cdd1d1 0))
                (declare-const Pu_ccd1d1 Int)
                (assert (= Pu_ccd1d1 0))
                (declare-const Pd_ccd1d1 Int)
                (assert (= Pd_ccd1d1 0))
                (declare-const Pu_aad1d2 Int)
                (assert (= Pu_aad1d2 0))
                (declare-const Pd_aad1d2 Int)
                (assert (= Pd_aad1d2 0))
                (declare-const Pu_abd1d2 Int)
                (assert (= Pu_abd1d2 0))
                (declare-const Pd_abd1d2 Int)
                (assert (= Pd_abd1d2 0))
                (declare-const Pu_add1d2 Int)
                (assert (= Pu_add1d2 0))
                (declare-const Pd_add1d2 Int)
                (assert (= Pd_add1d2 0))
                (declare-const Pu_acd1d2 Int)
                (assert (= Pu_acd1d2 0))
                (declare-const Pd_acd1d2 Int)
                (assert (= Pd_acd1d2 0))
                (declare-const Pu_bad1d2 Int)
                (assert (= Pu_bad1d2 0))
                (declare-const Pd_bad1d2 Int)
                (assert (= Pd_bad1d2 0))
                (declare-const Pu_bbd1d2 Int)
                (assert (= Pu_bbd1d2 0))
                (declare-const Pd_bbd1d2 Int)
                (assert (= Pd_bbd1d2 0))
                (declare-const Pu_bdd1d2 Int)
                (assert (= Pu_bdd1d2 1))
                (declare-const Pd_bdd1d2 Int)
                (assert (= Pd_bdd1d2 0))
                (declare-const Pu_bcd1d2 Int)
                (assert (= Pu_bcd1d2 0))
                (declare-const Pd_bcd1d2 Int)
                (assert (= Pd_bcd1d2 1))
                (declare-const Pu_dad1d2 Int)
                (assert (= Pu_dad1d2 0))
                (declare-const Pd_dad1d2 Int)
                (assert (= Pd_dad1d2 0))
                (declare-const Pu_dbd1d2 Int)
                (assert (= Pu_dbd1d2 0))
                (declare-const Pd_dbd1d2 Int)
                (assert (= Pd_dbd1d2 0))
                (declare-const Pu_ddd1d2 Int)
                (assert (= Pu_ddd1d2 0))
                (declare-const Pd_ddd1d2 Int)
                (assert (= Pd_ddd1d2 0))
                (declare-const Pu_dcd1d2 Int)
                (assert (= Pu_dcd1d2 0))
                (declare-const Pd_dcd1d2 Int)
                (assert (= Pd_dcd1d2 0))
                (declare-const Pu_cad1d2 Int)
                (assert (= Pu_cad1d2 0))
                (declare-const Pd_cad1d2 Int)
                (assert (= Pd_cad1d2 0))
                (declare-const Pu_cbd1d2 Int)
                (assert (= Pu_cbd1d2 0))
                (declare-const Pd_cbd1d2 Int)
                (assert (= Pd_cbd1d2 0))
                (declare-const Pu_cdd1d2 Int)
                (assert (= Pu_cdd1d2 0))
                (declare-const Pd_cdd1d2 Int)
                (assert (= Pd_cdd1d2 0))
                (declare-const Pu_ccd1d2 Int)
                (assert (= Pu_ccd1d2 0))
                (declare-const Pd_ccd1d2 Int)
                (assert (= Pd_ccd1d2 0))
                (declare-const Pu_aad2d0 Int)
                (assert (= Pu_aad2d0 0))
                (declare-const Pd_aad2d0 Int)
                (assert (= Pd_aad2d0 0))
                (declare-const Pu_abd2d0 Int)
                (assert (= Pu_abd2d0 0))
                (declare-const Pd_abd2d0 Int)
                (assert (= Pd_abd2d0 0))
                (declare-const Pu_add2d0 Int)
                (assert (= Pu_add2d0 0))
                (declare-const Pd_add2d0 Int)
                (assert (= Pd_add2d0 0))
                (declare-const Pu_acd2d0 Int)
                (assert (= Pu_acd2d0 0))
                (declare-const Pd_acd2d0 Int)
                (assert (= Pd_acd2d0 0))
                (declare-const Pu_bad2d0 Int)
                (assert (= Pu_bad2d0 0))
                (declare-const Pd_bad2d0 Int)
                (assert (= Pd_bad2d0 0))
                (declare-const Pu_bbd2d0 Int)
                (assert (= Pu_bbd2d0 0))
                (declare-const Pd_bbd2d0 Int)
                (assert (= Pd_bbd2d0 0))
                (declare-const Pu_bdd2d0 Int)
                (assert (= Pu_bdd2d0 0))
                (declare-const Pd_bdd2d0 Int)
                (assert (= Pd_bdd2d0 0))
                (declare-const Pu_bcd2d0 Int)
                (assert (= Pu_bcd2d0 0))
                (declare-const Pd_bcd2d0 Int)
                (assert (= Pd_bcd2d0 0))
                (declare-const Pu_dad2d0 Int)
                (assert (= Pu_dad2d0 1))
                (declare-const Pd_dad2d0 Int)
                (assert (= Pd_dad2d0 0))
                (declare-const Pu_dbd2d0 Int)
                (assert (= Pu_dbd2d0 0))
                (declare-const Pd_dbd2d0 Int)
                (assert (= Pd_dbd2d0 0))
                (declare-const Pu_ddd2d0 Int)
                (assert (= Pu_ddd2d0 0))
                (declare-const Pd_ddd2d0 Int)
                (assert (= Pd_ddd2d0 0))
                (declare-const Pu_dcd2d0 Int)
                (assert (= Pu_dcd2d0 0))
                (declare-const Pd_dcd2d0 Int)
                (assert (= Pd_dcd2d0 0))
                (declare-const Pu_cad2d0 Int)
                (assert (= Pu_cad2d0 0))
                (declare-const Pd_cad2d0 Int)
                (assert (= Pd_cad2d0 1))
                (declare-const Pu_cbd2d0 Int)
                (assert (= Pu_cbd2d0 0))
                (declare-const Pd_cbd2d0 Int)
                (assert (= Pd_cbd2d0 0))
                (declare-const Pu_cdd2d0 Int)
                (assert (= Pu_cdd2d0 0))
                (declare-const Pd_cdd2d0 Int)
                (assert (= Pd_cdd2d0 0))
                (declare-const Pu_ccd2d0 Int)
                (assert (= Pu_ccd2d0 0))
                (declare-const Pd_ccd2d0 Int)
                (assert (= Pd_ccd2d0 0))
                (declare-const Pu_aad2d1 Int)
                (assert (= Pu_aad2d1 0))
                (declare-const Pd_aad2d1 Int)
                (assert (= Pd_aad2d1 0))
                (declare-const Pu_abd2d1 Int)
                (assert (= Pu_abd2d1 0))
                (declare-const Pd_abd2d1 Int)
                (assert (= Pd_abd2d1 0))
                (declare-const Pu_add2d1 Int)
                (assert (= Pu_add2d1 0))
                (declare-const Pd_add2d1 Int)
                (assert (= Pd_add2d1 0))
                (declare-const Pu_acd2d1 Int)
                (assert (= Pu_acd2d1 0))
                (declare-const Pd_acd2d1 Int)
                (assert (= Pd_acd2d1 0))
                (declare-const Pu_bad2d1 Int)
                (assert (= Pu_bad2d1 0))
                (declare-const Pd_bad2d1 Int)
                (assert (= Pd_bad2d1 0))
                (declare-const Pu_bbd2d1 Int)
                (assert (= Pu_bbd2d1 0))
                (declare-const Pd_bbd2d1 Int)
                (assert (= Pd_bbd2d1 0))
                (declare-const Pu_bdd2d1 Int)
                (assert (= Pu_bdd2d1 0))
                (declare-const Pd_bdd2d1 Int)
                (assert (= Pd_bdd2d1 0))
                (declare-const Pu_bcd2d1 Int)
                (assert (= Pu_bcd2d1 0))
                (declare-const Pd_bcd2d1 Int)
                (assert (= Pd_bcd2d1 0))
                (declare-const Pu_dad2d1 Int)
                (assert (= Pu_dad2d1 0))
                (declare-const Pd_dad2d1 Int)
                (assert (= Pd_dad2d1 0))
                (declare-const Pu_dbd2d1 Int)
                (assert (= Pu_dbd2d1 1))
                (declare-const Pd_dbd2d1 Int)
                (assert (= Pd_dbd2d1 0))
                (declare-const Pu_ddd2d1 Int)
                (assert (= Pu_ddd2d1 0))
                (declare-const Pd_ddd2d1 Int)
                (assert (= Pd_ddd2d1 0))
                (declare-const Pu_dcd2d1 Int)
                (assert (= Pu_dcd2d1 0))
                (declare-const Pd_dcd2d1 Int)
                (assert (= Pd_dcd2d1 0))
                (declare-const Pu_cad2d1 Int)
                (assert (= Pu_cad2d1 0))
                (declare-const Pd_cad2d1 Int)
                (assert (= Pd_cad2d1 0))
                (declare-const Pu_cbd2d1 Int)
                (assert (= Pu_cbd2d1 0))
                (declare-const Pd_cbd2d1 Int)
                (assert (= Pd_cbd2d1 1))
                (declare-const Pu_cdd2d1 Int)
                (assert (= Pu_cdd2d1 0))
                (declare-const Pd_cdd2d1 Int)
                (assert (= Pd_cdd2d1 0))
                (declare-const Pu_ccd2d1 Int)
                (assert (= Pu_ccd2d1 0))
                (declare-const Pd_ccd2d1 Int)
                (assert (= Pd_ccd2d1 0))
                (declare-const Pu_aad2d2 Int)
                (assert (= Pu_aad2d2 0))
                (declare-const Pd_aad2d2 Int)
                (assert (= Pd_aad2d2 0))
                (declare-const Pu_abd2d2 Int)
                (assert (= Pu_abd2d2 0))
                (declare-const Pd_abd2d2 Int)
                (assert (= Pd_abd2d2 0))
                (declare-const Pu_add2d2 Int)
                (assert (= Pu_add2d2 0))
                (declare-const Pd_add2d2 Int)
                (assert (= Pd_add2d2 0))
                (declare-const Pu_acd2d2 Int)
                (assert (= Pu_acd2d2 0))
                (declare-const Pd_acd2d2 Int)
                (assert (= Pd_acd2d2 0))
                (declare-const Pu_bad2d2 Int)
                (assert (= Pu_bad2d2 0))
                (declare-const Pd_bad2d2 Int)
                (assert (= Pd_bad2d2 0))
                (declare-const Pu_bbd2d2 Int)
                (assert (= Pu_bbd2d2 0))
                (declare-const Pd_bbd2d2 Int)
                (assert (= Pd_bbd2d2 0))
                (declare-const Pu_bdd2d2 Int)
                (assert (= Pu_bdd2d2 0))
                (declare-const Pd_bdd2d2 Int)
                (assert (= Pd_bdd2d2 0))
                (declare-const Pu_bcd2d2 Int)
                (assert (= Pu_bcd2d2 0))
                (declare-const Pd_bcd2d2 Int)
                (assert (= Pd_bcd2d2 0))
                (declare-const Pu_dad2d2 Int)
                (assert (= Pu_dad2d2 0))
                (declare-const Pd_dad2d2 Int)
                (assert (= Pd_dad2d2 0))
                (declare-const Pu_dbd2d2 Int)
                (assert (= Pu_dbd2d2 0))
                (declare-const Pd_dbd2d2 Int)
                (assert (= Pd_dbd2d2 0))
                (declare-const Pu_ddd2d2 Int)
                (assert (= Pu_ddd2d2 1))
                (declare-const Pd_ddd2d2 Int)
                (assert (= Pd_ddd2d2 0))
                (declare-const Pu_dcd2d2 Int)
                (assert (= Pu_dcd2d2 0))
                (declare-const Pd_dcd2d2 Int)
                (assert (= Pd_dcd2d2 0))
                (declare-const Pu_cad2d2 Int)
                (assert (= Pu_cad2d2 0))
                (declare-const Pd_cad2d2 Int)
                (assert (= Pd_cad2d2 0))
                (declare-const Pu_cbd2d2 Int)
                (assert (= Pu_cbd2d2 0))
                (declare-const Pd_cbd2d2 Int)
                (assert (= Pd_cbd2d2 0))
                (declare-const Pu_cdd2d2 Int)
                (assert (= Pu_cdd2d2 0))
                (declare-const Pd_cdd2d2 Int)
                (assert (= Pd_cdd2d2 0))
                (declare-const Pu_ccd2d2 Int)
                (assert (= Pu_ccd2d2 0))
                (declare-const Pd_ccd2d2 Int)
                (assert (= Pd_ccd2d2 1))
                                
                (assert (= (+ (* Md0 Lu_ad0) (* Md1 Lu_ad1) (* Md2 Lu_ad2)) (+ (* Md0 Ld_ad0) (* Md1 Ld_ad1) (* Md2 Ld_ad2))  ))
                (assert (= (+ (* Md0 Lu_bd0) (* Md1 Lu_bd1) (* Md2 Lu_bd2)) (+ (* Md0 Ld_bd0) (* Md1 Ld_bd1) (* Md2 Ld_bd2))  ))
                (assert (= (+ (* Md0 Lu_dd0) (* Md1 Lu_dd1) (* Md2 Lu_dd2)) (+ (* Md0 Ld_dd0) (* Md1 Ld_dd1) (* Md2 Ld_dd2))  ))
                (assert (= (+ (* Md0 Lu_cd0) (* Md1 Lu_cd1) (* Md2 Lu_cd2)) (+ (* Md0 Ld_cd0) (* Md1 Ld_cd1) (* Md2 Ld_cd2))  ))
                                
                (assert (= (+(* Md0 Pu_aad0)(* Md1 Pu_aad1)(* Md2 Pu_aad2)(* Md0d0 Pu_aad0d0)(* Md0d1 Pu_aad0d1)(* Md0d2 Pu_aad0d2)(* Md1d0 Pu_aad1d0)(* Md1d1 Pu_aad1d1)(* Md1d2 Pu_aad1d2)(* Md2d0 Pu_aad2d0)(* Md2d1 Pu_aad2d1)(* Md2d2 Pu_aad2d2)) (+ (* Md0 Pd_aad0)(* Md1 Pd_aad1)(* Md2 Pd_aad2)(* Md0d0 Pd_aad0d0)(* Md0d1 Pd_aad0d1)(* Md0d2 Pd_aad0d2)(* Md1d0 Pd_aad1d0)(* Md1d1 Pd_aad1d1)(* Md1d2 Pd_aad1d2)(* Md2d0 Pd_aad2d0)(* Md2d1 Pd_aad2d1)(* Md2d2 Pd_aad2d2))))
                (assert (= (+(* Md0 Pu_abd0)(* Md1 Pu_abd1)(* Md2 Pu_abd2)(* Md0d0 Pu_abd0d0)(* Md0d1 Pu_abd0d1)(* Md0d2 Pu_abd0d2)(* Md1d0 Pu_abd1d0)(* Md1d1 Pu_abd1d1)(* Md1d2 Pu_abd1d2)(* Md2d0 Pu_abd2d0)(* Md2d1 Pu_abd2d1)(* Md2d2 Pu_abd2d2)) (+ (* Md0 Pd_abd0)(* Md1 Pd_abd1)(* Md2 Pd_abd2)(* Md0d0 Pd_abd0d0)(* Md0d1 Pd_abd0d1)(* Md0d2 Pd_abd0d2)(* Md1d0 Pd_abd1d0)(* Md1d1 Pd_abd1d1)(* Md1d2 Pd_abd1d2)(* Md2d0 Pd_abd2d0)(* Md2d1 Pd_abd2d1)(* Md2d2 Pd_abd2d2))))
                (assert (= (+(* Md0 Pu_add0)(* Md1 Pu_add1)(* Md2 Pu_add2)(* Md0d0 Pu_add0d0)(* Md0d1 Pu_add0d1)(* Md0d2 Pu_add0d2)(* Md1d0 Pu_add1d0)(* Md1d1 Pu_add1d1)(* Md1d2 Pu_add1d2)(* Md2d0 Pu_add2d0)(* Md2d1 Pu_add2d1)(* Md2d2 Pu_add2d2)) (+ (* Md0 Pd_add0)(* Md1 Pd_add1)(* Md2 Pd_add2)(* Md0d0 Pd_add0d0)(* Md0d1 Pd_add0d1)(* Md0d2 Pd_add0d2)(* Md1d0 Pd_add1d0)(* Md1d1 Pd_add1d1)(* Md1d2 Pd_add1d2)(* Md2d0 Pd_add2d0)(* Md2d1 Pd_add2d1)(* Md2d2 Pd_add2d2))))
                (assert (= (+(* Md0 Pu_acd0)(* Md1 Pu_acd1)(* Md2 Pu_acd2)(* Md0d0 Pu_acd0d0)(* Md0d1 Pu_acd0d1)(* Md0d2 Pu_acd0d2)(* Md1d0 Pu_acd1d0)(* Md1d1 Pu_acd1d1)(* Md1d2 Pu_acd1d2)(* Md2d0 Pu_acd2d0)(* Md2d1 Pu_acd2d1)(* Md2d2 Pu_acd2d2)) (+ (* Md0 Pd_acd0)(* Md1 Pd_acd1)(* Md2 Pd_acd2)(* Md0d0 Pd_acd0d0)(* Md0d1 Pd_acd0d1)(* Md0d2 Pd_acd0d2)(* Md1d0 Pd_acd1d0)(* Md1d1 Pd_acd1d1)(* Md1d2 Pd_acd1d2)(* Md2d0 Pd_acd2d0)(* Md2d1 Pd_acd2d1)(* Md2d2 Pd_acd2d2))))
                (assert (= (+(* Md0 Pu_bad0)(* Md1 Pu_bad1)(* Md2 Pu_bad2)(* Md0d0 Pu_bad0d0)(* Md0d1 Pu_bad0d1)(* Md0d2 Pu_bad0d2)(* Md1d0 Pu_bad1d0)(* Md1d1 Pu_bad1d1)(* Md1d2 Pu_bad1d2)(* Md2d0 Pu_bad2d0)(* Md2d1 Pu_bad2d1)(* Md2d2 Pu_bad2d2)) (+ (* Md0 Pd_bad0)(* Md1 Pd_bad1)(* Md2 Pd_bad2)(* Md0d0 Pd_bad0d0)(* Md0d1 Pd_bad0d1)(* Md0d2 Pd_bad0d2)(* Md1d0 Pd_bad1d0)(* Md1d1 Pd_bad1d1)(* Md1d2 Pd_bad1d2)(* Md2d0 Pd_bad2d0)(* Md2d1 Pd_bad2d1)(* Md2d2 Pd_bad2d2))))
                (assert (= (+(* Md0 Pu_bbd0)(* Md1 Pu_bbd1)(* Md2 Pu_bbd2)(* Md0d0 Pu_bbd0d0)(* Md0d1 Pu_bbd0d1)(* Md0d2 Pu_bbd0d2)(* Md1d0 Pu_bbd1d0)(* Md1d1 Pu_bbd1d1)(* Md1d2 Pu_bbd1d2)(* Md2d0 Pu_bbd2d0)(* Md2d1 Pu_bbd2d1)(* Md2d2 Pu_bbd2d2)) (+ (* Md0 Pd_bbd0)(* Md1 Pd_bbd1)(* Md2 Pd_bbd2)(* Md0d0 Pd_bbd0d0)(* Md0d1 Pd_bbd0d1)(* Md0d2 Pd_bbd0d2)(* Md1d0 Pd_bbd1d0)(* Md1d1 Pd_bbd1d1)(* Md1d2 Pd_bbd1d2)(* Md2d0 Pd_bbd2d0)(* Md2d1 Pd_bbd2d1)(* Md2d2 Pd_bbd2d2))))
                (assert (= (+(* Md0 Pu_bdd0)(* Md1 Pu_bdd1)(* Md2 Pu_bdd2)(* Md0d0 Pu_bdd0d0)(* Md0d1 Pu_bdd0d1)(* Md0d2 Pu_bdd0d2)(* Md1d0 Pu_bdd1d0)(* Md1d1 Pu_bdd1d1)(* Md1d2 Pu_bdd1d2)(* Md2d0 Pu_bdd2d0)(* Md2d1 Pu_bdd2d1)(* Md2d2 Pu_bdd2d2)) (+ (* Md0 Pd_bdd0)(* Md1 Pd_bdd1)(* Md2 Pd_bdd2)(* Md0d0 Pd_bdd0d0)(* Md0d1 Pd_bdd0d1)(* Md0d2 Pd_bdd0d2)(* Md1d0 Pd_bdd1d0)(* Md1d1 Pd_bdd1d1)(* Md1d2 Pd_bdd1d2)(* Md2d0 Pd_bdd2d0)(* Md2d1 Pd_bdd2d1)(* Md2d2 Pd_bdd2d2))))
                (assert (= (+(* Md0 Pu_bcd0)(* Md1 Pu_bcd1)(* Md2 Pu_bcd2)(* Md0d0 Pu_bcd0d0)(* Md0d1 Pu_bcd0d1)(* Md0d2 Pu_bcd0d2)(* Md1d0 Pu_bcd1d0)(* Md1d1 Pu_bcd1d1)(* Md1d2 Pu_bcd1d2)(* Md2d0 Pu_bcd2d0)(* Md2d1 Pu_bcd2d1)(* Md2d2 Pu_bcd2d2)) (+ (* Md0 Pd_bcd0)(* Md1 Pd_bcd1)(* Md2 Pd_bcd2)(* Md0d0 Pd_bcd0d0)(* Md0d1 Pd_bcd0d1)(* Md0d2 Pd_bcd0d2)(* Md1d0 Pd_bcd1d0)(* Md1d1 Pd_bcd1d1)(* Md1d2 Pd_bcd1d2)(* Md2d0 Pd_bcd2d0)(* Md2d1 Pd_bcd2d1)(* Md2d2 Pd_bcd2d2))))
                (assert (= (+(* Md0 Pu_dad0)(* Md1 Pu_dad1)(* Md2 Pu_dad2)(* Md0d0 Pu_dad0d0)(* Md0d1 Pu_dad0d1)(* Md0d2 Pu_dad0d2)(* Md1d0 Pu_dad1d0)(* Md1d1 Pu_dad1d1)(* Md1d2 Pu_dad1d2)(* Md2d0 Pu_dad2d0)(* Md2d1 Pu_dad2d1)(* Md2d2 Pu_dad2d2)) (+ (* Md0 Pd_dad0)(* Md1 Pd_dad1)(* Md2 Pd_dad2)(* Md0d0 Pd_dad0d0)(* Md0d1 Pd_dad0d1)(* Md0d2 Pd_dad0d2)(* Md1d0 Pd_dad1d0)(* Md1d1 Pd_dad1d1)(* Md1d2 Pd_dad1d2)(* Md2d0 Pd_dad2d0)(* Md2d1 Pd_dad2d1)(* Md2d2 Pd_dad2d2))))
                (assert (= (+(* Md0 Pu_dbd0)(* Md1 Pu_dbd1)(* Md2 Pu_dbd2)(* Md0d0 Pu_dbd0d0)(* Md0d1 Pu_dbd0d1)(* Md0d2 Pu_dbd0d2)(* Md1d0 Pu_dbd1d0)(* Md1d1 Pu_dbd1d1)(* Md1d2 Pu_dbd1d2)(* Md2d0 Pu_dbd2d0)(* Md2d1 Pu_dbd2d1)(* Md2d2 Pu_dbd2d2)) (+ (* Md0 Pd_dbd0)(* Md1 Pd_dbd1)(* Md2 Pd_dbd2)(* Md0d0 Pd_dbd0d0)(* Md0d1 Pd_dbd0d1)(* Md0d2 Pd_dbd0d2)(* Md1d0 Pd_dbd1d0)(* Md1d1 Pd_dbd1d1)(* Md1d2 Pd_dbd1d2)(* Md2d0 Pd_dbd2d0)(* Md2d1 Pd_dbd2d1)(* Md2d2 Pd_dbd2d2))))
                (assert (= (+(* Md0 Pu_ddd0)(* Md1 Pu_ddd1)(* Md2 Pu_ddd2)(* Md0d0 Pu_ddd0d0)(* Md0d1 Pu_ddd0d1)(* Md0d2 Pu_ddd0d2)(* Md1d0 Pu_ddd1d0)(* Md1d1 Pu_ddd1d1)(* Md1d2 Pu_ddd1d2)(* Md2d0 Pu_ddd2d0)(* Md2d1 Pu_ddd2d1)(* Md2d2 Pu_ddd2d2)) (+ (* Md0 Pd_ddd0)(* Md1 Pd_ddd1)(* Md2 Pd_ddd2)(* Md0d0 Pd_ddd0d0)(* Md0d1 Pd_ddd0d1)(* Md0d2 Pd_ddd0d2)(* Md1d0 Pd_ddd1d0)(* Md1d1 Pd_ddd1d1)(* Md1d2 Pd_ddd1d2)(* Md2d0 Pd_ddd2d0)(* Md2d1 Pd_ddd2d1)(* Md2d2 Pd_ddd2d2))))
                (assert (= (+(* Md0 Pu_dcd0)(* Md1 Pu_dcd1)(* Md2 Pu_dcd2)(* Md0d0 Pu_dcd0d0)(* Md0d1 Pu_dcd0d1)(* Md0d2 Pu_dcd0d2)(* Md1d0 Pu_dcd1d0)(* Md1d1 Pu_dcd1d1)(* Md1d2 Pu_dcd1d2)(* Md2d0 Pu_dcd2d0)(* Md2d1 Pu_dcd2d1)(* Md2d2 Pu_dcd2d2)) (+ (* Md0 Pd_dcd0)(* Md1 Pd_dcd1)(* Md2 Pd_dcd2)(* Md0d0 Pd_dcd0d0)(* Md0d1 Pd_dcd0d1)(* Md0d2 Pd_dcd0d2)(* Md1d0 Pd_dcd1d0)(* Md1d1 Pd_dcd1d1)(* Md1d2 Pd_dcd1d2)(* Md2d0 Pd_dcd2d0)(* Md2d1 Pd_dcd2d1)(* Md2d2 Pd_dcd2d2))))
                (assert (= (+(* Md0 Pu_cad0)(* Md1 Pu_cad1)(* Md2 Pu_cad2)(* Md0d0 Pu_cad0d0)(* Md0d1 Pu_cad0d1)(* Md0d2 Pu_cad0d2)(* Md1d0 Pu_cad1d0)(* Md1d1 Pu_cad1d1)(* Md1d2 Pu_cad1d2)(* Md2d0 Pu_cad2d0)(* Md2d1 Pu_cad2d1)(* Md2d2 Pu_cad2d2)) (+ (* Md0 Pd_cad0)(* Md1 Pd_cad1)(* Md2 Pd_cad2)(* Md0d0 Pd_cad0d0)(* Md0d1 Pd_cad0d1)(* Md0d2 Pd_cad0d2)(* Md1d0 Pd_cad1d0)(* Md1d1 Pd_cad1d1)(* Md1d2 Pd_cad1d2)(* Md2d0 Pd_cad2d0)(* Md2d1 Pd_cad2d1)(* Md2d2 Pd_cad2d2))))
                (assert (= (+(* Md0 Pu_cbd0)(* Md1 Pu_cbd1)(* Md2 Pu_cbd2)(* Md0d0 Pu_cbd0d0)(* Md0d1 Pu_cbd0d1)(* Md0d2 Pu_cbd0d2)(* Md1d0 Pu_cbd1d0)(* Md1d1 Pu_cbd1d1)(* Md1d2 Pu_cbd1d2)(* Md2d0 Pu_cbd2d0)(* Md2d1 Pu_cbd2d1)(* Md2d2 Pu_cbd2d2)) (+ (* Md0 Pd_cbd0)(* Md1 Pd_cbd1)(* Md2 Pd_cbd2)(* Md0d0 Pd_cbd0d0)(* Md0d1 Pd_cbd0d1)(* Md0d2 Pd_cbd0d2)(* Md1d0 Pd_cbd1d0)(* Md1d1 Pd_cbd1d1)(* Md1d2 Pd_cbd1d2)(* Md2d0 Pd_cbd2d0)(* Md2d1 Pd_cbd2d1)(* Md2d2 Pd_cbd2d2))))
                (assert (= (+(* Md0 Pu_cdd0)(* Md1 Pu_cdd1)(* Md2 Pu_cdd2)(* Md0d0 Pu_cdd0d0)(* Md0d1 Pu_cdd0d1)(* Md0d2 Pu_cdd0d2)(* Md1d0 Pu_cdd1d0)(* Md1d1 Pu_cdd1d1)(* Md1d2 Pu_cdd1d2)(* Md2d0 Pu_cdd2d0)(* Md2d1 Pu_cdd2d1)(* Md2d2 Pu_cdd2d2)) (+ (* Md0 Pd_cdd0)(* Md1 Pd_cdd1)(* Md2 Pd_cdd2)(* Md0d0 Pd_cdd0d0)(* Md0d1 Pd_cdd0d1)(* Md0d2 Pd_cdd0d2)(* Md1d0 Pd_cdd1d0)(* Md1d1 Pd_cdd1d1)(* Md1d2 Pd_cdd1d2)(* Md2d0 Pd_cdd2d0)(* Md2d1 Pd_cdd2d1)(* Md2d2 Pd_cdd2d2))))
                (assert (= (+(* Md0 Pu_ccd0)(* Md1 Pu_ccd1)(* Md2 Pu_ccd2)(* Md0d0 Pu_ccd0d0)(* Md0d1 Pu_ccd0d1)(* Md0d2 Pu_ccd0d2)(* Md1d0 Pu_ccd1d0)(* Md1d1 Pu_ccd1d1)(* Md1d2 Pu_ccd1d2)(* Md2d0 Pu_ccd2d0)(* Md2d1 Pu_ccd2d1)(* Md2d2 Pu_ccd2d2)) (+ (* Md0 Pd_ccd0)(* Md1 Pd_ccd1)(* Md2 Pd_ccd2)(* Md0d0 Pd_ccd0d0)(* Md0d1 Pd_ccd0d1)(* Md0d2 Pd_ccd0d2)(* Md1d0 Pd_ccd1d0)(* Md1d1 Pd_ccd1d1)(* Md1d2 Pd_ccd1d2)(* Md2d0 Pd_ccd2d0)(* Md2d1 Pd_ccd2d1)(* Md2d2 Pd_ccd2d2))))
                (check-sat)
                (get-model)
                                
                """);
        log.info(body);
        return ResponseEntity.ok().body(body);
    }

    public String smtGen(String string) {
        try (Context context = new Context()) {
            Solver solver = context.mkSimpleSolver();
            solver.fromString(string);
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
