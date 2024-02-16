package ru.bmstu.iu9.tfl_lab_lib_smt.utils;

import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import lombok.experimental.UtilityClass;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.SMT2;

import static com.microsoft.z3.Status.SATISFIABLE;

@UtilityClass
public class SMTUtils {
    public Status check(SMT2 smt2) {
        try (Context context = new Context()) {
            Solver solver = context.mkSimpleSolver();
            solver.fromString(smt2.toString());
            return solver.check();
        }
    }

    public Model getModel(SMT2 smt2) {
        System.out.println(smt2.toString());
        Context context = new Context();
        Solver solver = context.mkSimpleSolver();
        solver.fromString(smt2.toString());
        if (solver.check().equals(SATISFIABLE)) {
            return solver.getModel();
        }
        return null;
    }
}
