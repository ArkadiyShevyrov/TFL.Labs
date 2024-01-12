package ru.bmstu.iu9.tfl_lab_lib.utils.converter;

import java.util.List;

public class MatrixPower {
    // Метод для умножения матриц A на саму k раз
    public static int[][] matrixPower(int[][] A, int k) {
        int rows = A.length;
        int cols = A[0].length;

        // Создаем единичную матрицу
        int[][] result = new int[rows][cols];
        for (int i = 0; i < rows; i++) {
            for (int j = 0; j < cols; j++) {
                result[i][j] = (i == j) ? 1 : 0;
            }
        }

        // Умножаем матрицу на саму k раз
        for (int i = 0; i < k; i++) {
            result = multiplyMatrices(result, A);
        }

        return result;
    }

    // Метод для умножения двух матриц
    private static int[][] multiplyMatrices(int[][] A, int[][] B) {
        int rowsA = A.length;
        int colsA = A[0].length;
        int colsB = B[0].length;

        int[][] result = new int[rowsA][colsB];

        for (int i = 0; i < rowsA; i++) {
            for (int j = 0; j < colsB; j++) {
                for (int k = 0; k < colsA; k++) {
                    result[i][j] += A[i][k] * B[k][j];
                }
            }
        }

        return result;
    }

    public static int[][] matrixDisjunction(List<int[][]> matrices) {
        if (matrices == null || matrices.isEmpty()) {
            // Возвращаем null или выбрасываем исключение, в зависимости от требований
            return null;
        }

        int rows = matrices.get(0).length;
        int cols = matrices.get(0)[0].length;

        // Создаем матрицу-результат, заполненную нулями
        int[][] result = new int[rows][cols];

        // Выполняем дизъюнкцию матриц
        for (int[][] matrix : matrices) {
            for (int i = 0; i < rows; i++) {
                for (int j = 0; j < cols; j++) {
                    result[i][j] |= matrix[i][j];
                }
            }
        }

        return result;
    }
}