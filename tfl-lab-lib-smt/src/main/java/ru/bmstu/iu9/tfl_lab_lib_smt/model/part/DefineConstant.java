package ru.bmstu.iu9.tfl_lab_lib_smt.model.part;

import lombok.AllArgsConstructor;
import lombok.Getter;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.Term;

@Getter
@AllArgsConstructor
public class DefineConstant {
    private Term term;
    private Type type;
    private String value;

    @Override
    public String toString() {
        return "(define-const " + term + " " + type + " " + value + ")";
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
