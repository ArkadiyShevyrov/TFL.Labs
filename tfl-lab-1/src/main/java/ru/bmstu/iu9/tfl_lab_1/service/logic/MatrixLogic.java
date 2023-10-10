package ru.bmstu.iu9.tfl_lab_1.service.logic;

import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.basic.ValueTerm;
import ru.bmstu.iu9.tfl_lab_1.model.smt.term.custom.*;

@UtilityClass
public class MatrixLogic {
    public MatrixA generateMatrixByX(String string) {
        if (string.length() == 1) {
            return newMatrixAWithName(string);
        }
        MatrixA matrixOne = newMatrixAWithName(String.valueOf(string.charAt(0)));
        for (int i = 1; i < string.length(); i++) {
            char c = string.charAt(i);
            MatrixA matrixTwo = newMatrixAWithName(String.valueOf(c));
            matrixOne = multiplexMatrixAA(matrixOne, matrixTwo);
        }
        return matrixOne;
    }

    public MatrixB generateMatrixByC(String string) {
        if (string.length() == 1) {
            return newMatrixBWithName(string);
        }
        MatrixB matrixTwo = newMatrixBWithName(String.valueOf(string.charAt(0)));
        for (int i = 1; i < string.length(); i++) {
            char c = string.charAt(i);
            MatrixA matrixA = generateMatrixByX(string.substring(0, i));
            MatrixB matrixB = newMatrixBWithName(String.valueOf(c));
            MatrixB matrixOne = multiplexMatrixAB(matrixA, matrixB);
            matrixTwo = sumMatrixBB(matrixOne, matrixTwo);
        }
        return matrixTwo;
    }

    public MatrixA newMatrixAWithName(String name) {
        return new MatrixA(
                new ValueTerm("a" + name + "00"),
                new ValueTerm("a" + name + "01"),
                new ValueTerm("a" + name + "10"),
                new ValueTerm("a" + name + "11"));
    }

    public MatrixB newMatrixBWithName(String name) {
        return new MatrixB(
                new ValueTerm("b" + name + "0"),
                new ValueTerm("b" + name + "1"));
    }

    public MatrixA multiplexMatrixAA(MatrixA matrixOne, MatrixA matrixTwo) {
        return new MatrixA(
                new ArcticMaxTerm(
                        new ArcticSumTerm(matrixOne.getTerm00(), matrixTwo.getTerm00()),
                        new ArcticSumTerm(matrixOne.getTerm01(), matrixTwo.getTerm10())),
                new ArcticMaxTerm(
                        new ArcticSumTerm(matrixOne.getTerm00(), matrixTwo.getTerm01()),
                        new ArcticSumTerm(matrixOne.getTerm01(), matrixTwo.getTerm11())),
                new ArcticMaxTerm(
                        new ArcticSumTerm(matrixOne.getTerm10(), matrixTwo.getTerm00()),
                        new ArcticSumTerm(matrixOne.getTerm11(), matrixTwo.getTerm10())),
                new ArcticMaxTerm(
                        new ArcticSumTerm(matrixOne.getTerm10(), matrixTwo.getTerm01()),
                        new ArcticSumTerm(matrixOne.getTerm11(), matrixTwo.getTerm11()))
        );
    }

    public MatrixB multiplexMatrixAB(MatrixA matrixOne, MatrixB matrixTwo) {
        return new MatrixB(
                new ArcticMaxTerm(
                        new ArcticSumTerm(matrixOne.getTerm00(), matrixTwo.getTerm0()),
                        new ArcticSumTerm(matrixOne.getTerm01(), matrixTwo.getTerm1())),
                new ArcticMaxTerm(
                        new ArcticSumTerm(matrixOne.getTerm10(), matrixTwo.getTerm0()),
                        new ArcticSumTerm(matrixOne.getTerm11(), matrixTwo.getTerm1()))
        );
    }

    public MatrixB sumMatrixBB(MatrixB matrixOne, MatrixB matrixTwo) {
        return new MatrixB(
                new ArcticSumTerm(matrixOne.getTerm0(), matrixTwo.getTerm0()),
                new ArcticSumTerm(matrixOne.getTerm1(), matrixTwo.getTerm1())
        );
    }

    public MatrixA moreMatrixAA(MatrixA matrixOne, MatrixA matrixTwo) {
        return new MatrixA(
                new ArcticMoreTerm(matrixOne.getTerm00(), matrixTwo.getTerm00()),
                new ArcticMoreTerm(matrixOne.getTerm01(), matrixTwo.getTerm01()),
                new ArcticMoreTerm(matrixOne.getTerm10(), matrixTwo.getTerm10()),
                new ArcticMoreTerm(matrixOne.getTerm11(), matrixTwo.getTerm11())
        );
    }

    public MatrixB moreMatrixBB(MatrixB matrixOne, MatrixB matrixTwo) {
        return new MatrixB(
                new ArcticMoreTerm(matrixOne.getTerm0(), matrixTwo.getTerm0()),
                new ArcticMoreTerm(matrixOne.getTerm1(), matrixTwo.getTerm1())
        );
    }
}
