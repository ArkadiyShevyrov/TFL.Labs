import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import org.junit.jupiter.api.Test;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.boot.test.context.TestConfiguration;
import org.springframework.context.annotation.ComponentScan;
import org.springframework.test.context.ContextConfiguration;
import ru.bmstu.iu9.tfl_lab_2.controller.CController;
import ru.bmstu.iu9.tfl_lab_2.service.OptimizationService;
import java.util.ArrayList;
import java.util.List;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ApplicationTests {
    private final OptimizationService optimizationService = new OptimizationService();

    @Test
    void test1() {
        List<TestA> list = new ArrayList<>();
        list.add(new TestA("(abc)***", "(abc)*"));
        list.add(new TestA("((abc)*|(cde)*)*", "(abc|cde)*"));
        list.add(new TestA("(abc(cde)*)*", "(abc(cde)*)*"));
        list.add(new TestA("((abc)*(cde)*)*", "(abc|cde)*"));
//        list.add(new TestA("", ""));
//        list.add(new TestA("", ""));
//        list.add(new TestA("", ""));
//        list.add(new TestA("", ""));
//        list.add(new TestA("", ""));
        for (TestA testA : list) {
            assertEquals(optimizationService.optimization(testA.input), testA.expected);
        }
    }

    @Getter
    @AllArgsConstructor
    static class TestA {
        private String input;
        private String expected;
    }
}
