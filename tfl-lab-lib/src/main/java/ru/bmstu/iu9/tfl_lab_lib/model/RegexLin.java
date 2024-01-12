package ru.bmstu.iu9.tfl_lab_lib.model;

import lombok.Getter;
import lombok.extern.slf4j.Slf4j;

@Slf4j
@Getter
public class RegexLin extends Regex {
    int linNumber;
    public RegexLin(Regex regex, int linNumber) {
        super(regex.getType(), regex.getValue(), regex.getLeft(), regex.getRight());
        this.linNumber = linNumber;
    }

    public RegexLin(Type type) {
        super(type);
    }

    public RegexLin(Type type, RegexLin left) {
        super(type, left);
    }

    public RegexLin(Type type, RegexLin left, RegexLin right) {
        super(type, left, right);
    }


    public int compareTo(RegexLin r) {
        if (this.linNumber == r.linNumber) {
            return this.compareTo((Regex) r);
        } else {
            return this.linNumber - r.linNumber;
        }
    }

    @Override
    public String toString() {
        if (linNumber != 0) {
            return super.toString() + linNumber;
        } else {
            return super.toString();
        }
    }
}
