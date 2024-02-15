package ru.bmstu.iu9.tfl_lab_1_null.model.rest;

import lombok.Getter;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

@Getter
public class Domino {
    String up;
    String down;

    @Override
    public String toString() {
        return "(" + up + "," + down + ")";
    }

    public Domino(String dominoString) {
        String regex = "\\((\\w+),(\\w+)\\)";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(dominoString);
        if (!matcher.find()) {
            return;
        }
        this.up = matcher.group(1);
        this.down = matcher.group(2);
    }
}
