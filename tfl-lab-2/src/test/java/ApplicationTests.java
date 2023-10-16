import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_2.service.OptimizationService;
import java.util.ArrayList;
import java.util.List;
import static org.junit.jupiter.api.Assertions.assertEquals;

@Slf4j
class ApplicationTests {
    private final OptimizationService optimizationService = new OptimizationService();

    @Test
    void test1() {
        List<TestA> list = new ArrayList<>();
        list.add(new TestA("(abc)***", "(abc)*"));
        list.add(new TestA("((abc)*|(cde)*)*", "(abc|cde)*"));
        list.add(new TestA("(abc(cde)*)*", "(abc(cde)*)*"));
        list.add(new TestA("((abc)*(cde)*)*", "(abc|cde)*"));
//        list.add(new TestA("(((a|c|(a|b)c|c|(a|b)c|c|a(b|c)|a|b|a)|b)*|((acd)e)*)*", "(a|ab|ac|ac|acde|b|bc|c)*"));
        list.add(new TestA("ac|bc","(a|b)c"));
        list.add(new TestA("ab|ac","a(b|c)"));
        list.add(new TestA("a*a|a*c", "a*(a|c)"));
        list.add(new TestA("a*a|b|a*c", "a*(a|c)|b"));

        for (TestA testA : list) {
            String optimization = optimizationService.optimization(testA.input);
            assertEquals(testA.expected, optimization);
        }
    }

    @Getter
    @AllArgsConstructor
    static class TestA {
        private String input;
        private String expected;
    }
}
