package ru.bmstu.iu9.tfl_lab_lib_smt.model.part;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;

@Getter
@AllArgsConstructor
public class DeclareFunction {
    private Term term;
    private Type type;

    @Override
    public String toString() {
        return "(declare-fun " + term + " " + type + ")";
    }

    public enum Type {
        INT;

        @Override
        public String toString() {
            return switch (this) {
                case INT -> "Int";
            };
        }
    }
}
