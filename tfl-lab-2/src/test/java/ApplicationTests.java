import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import org.junit.jupiter.api.Test;
import ru.bmstu.iu9.tfl_lab_2.model.Tree;
import ru.bmstu.iu9.tfl_lab_2.service.OptimizationService;
import ru.bmstu.iu9.tfl_lab_2.utils.DSTR;
import java.util.ArrayList;
import java.util.List;
import static org.junit.jupiter.api.Assertions.assertEquals;

@Slf4j
class ApplicationTests {
    private final OptimizationService optimizationService = new OptimizationService();

    @Test
    void test1() {
        List<TestA> list = new ArrayList<>();
//        list.add(new TestA("(abc)***", "(abc)*"));
//        list.add(new TestA("((abc)*|(cde)*)*", "(abc|cde)*"));
//        list.add(new TestA("(abc(cde)*)*", "(abc(cde)*)*"));
//        list.add(new TestA("((abc)*(cde)*)*", "(abc|cde)*"));
//        list.add(new TestA("ac|bc","(a|b)c"));
//        list.add(new TestA("ab|ac","a(b|c)"));
//        list.add(new TestA("a*a|a*c", "a*(a|c)"));
//        list.add(new TestA("a*a|b|a*c", "a*(a|c)|b"));
//        list.add(new TestA("(((c|a(b|c)|b|a)|b)*|((acd)e)*)*", "(a|a(b|c|cde)|b|c)*"));
//        list.add(new TestA("(acde|a(b|c))","a(b|c|cde)"));
//        list.add(new TestA("(acde|agz|acdf|ab|ac))","a(b|c|cd(e|f)|gz)"));
//        list.add(new TestA("abcdefghij|abcdefghi|abcdefgh|abcdefg|abcdef|abcde|abcd|abc|ab|a",
//                "a|a(b|b(c|c(d|d(e|e(f|f(g|g(h|h(i|ij))))))))"));
//        list.add(new TestA("abbba|adddda", "a(bbb|dddd)a"));
        list.add(new TestA("abcdefg|bcdefg|cdefg|defg|efg|fg|g", ""));
        for (TestA testA : list) {
            String optimization = optimizationService.optimization(testA.input);
            assertEquals(testA.expected, optimization);
        }
//        Tree tree = new Tree(
//                Tree.Type.CONCAT,
//                new Tree(Tree.Type.SYMBOL, "a"),
//                new Tree(Tree.Type.CONCAT,
//                        new Tree(Tree.Type.SYMBOL, "b"),
//                        new Tree(Tree.Type.CONCAT,
//                                new Tree(Tree.Type.SYMBOL, "c"),
//                                new Tree(Tree.Type.CONCAT,
//                                        new Tree(Tree.Type.SYMBOL, "d"),
//                                        new Tree(Tree.Type.SYMBOL, "e")))
//                ));
//        log.info(Tree.drawTree(DSTR.getConcatNotLast(tree)));
    }

    @Getter
    @AllArgsConstructor
    static class TestA {
        private String input;
        private String expected;
    }
}
