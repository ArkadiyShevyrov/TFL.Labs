package ru.bmstu.iu9.tfl_lab_1;

import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.http.ResponseEntity;
import ru.bmstu.iu9.tfl_lab_1.controller.Controller;
import ru.bmstu.iu9.tfl_lab_1.model.rest.SrsString;
import java.util.ArrayList;
import static org.junit.jupiter.api.Assertions.assertEquals;

@SpringBootTest
class ApplicationTests {
    @Autowired
    private Controller controller;

    @Test
    void test1() {
        ArrayList<SrsString> SrsStrings = new ArrayList<>();
        SrsStrings.add(new SrsString("ff->f"));
        ResponseEntity<String> stringResponseEntity = controller.create(SrsStrings);
        assertEquals(stringResponseEntity.getBody(), "SATISFIABLE");
    }

    @Test
    void test2() {
        ArrayList<SrsString> SrsStrings = new ArrayList<>();
        SrsStrings.add(new SrsString("f->ff"));
        ResponseEntity<String> stringResponseEntity = controller.create(SrsStrings);
        assertEquals(stringResponseEntity.getBody(), "UNSATISFIABLE");
    }
}
