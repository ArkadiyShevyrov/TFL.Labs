package ru.bmstu.iu9.tfl_lab_lib_smt.utils;

import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import lombok.experimental.UtilityClass;

import static com.microsoft.z3.Status.SATISFIABLE;

@UtilityClass
public class SMTUtils {
    public Status check(String smtInput) {
        try (Context context = new Context()) {
            Solver solver = context.mkSimpleSolver();
            solver.fromString(smtInput);
            return solver.check();
        }
    }

    public Model getModel(String smtInput) {
        try (Context context = new Context()) {
            Solver solver = context.mkSimpleSolver();
            solver.fromString(smtInput);
            if (solver.check().equals(SATISFIABLE)) {
                return solver.getModel();
            }
            return null;
        }
    }
}
