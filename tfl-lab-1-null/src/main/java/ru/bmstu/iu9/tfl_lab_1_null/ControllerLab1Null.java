package ru.bmstu.iu9.tfl_lab_1_null;

import com.microsoft.z3.Model;
import com.microsoft.z3.Status;
import io.swagger.v3.oas.annotations.Operation;
import io.swagger.v3.oas.annotations.Parameter;
import io.swagger.v3.oas.annotations.tags.Tag;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import ru.bmstu.iu9.tfl_lab_1_null.model.Domino;
import ru.bmstu.iu9.tfl_lab_lib_smt.model.SMT2;
import ru.bmstu.iu9.tfl_lab_lib_smt.utils.SMTUtils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

@Slf4j
@Tag(name = "Lab1-null", description = "Lab 1-null description")
@RestController
@RequestMapping("/rest/lab-1-null")
@RequiredArgsConstructor
public class ControllerLab1Null {
    @Operation(description = "Проверка существования решения проблем соответствия Поста")
    @PostMapping(value = "/checkSolutionsProblemsPostCompliance")
    public ResponseEntity<String> getStatusCheck(
            @Parameter(description = "problem")
            @RequestBody String problem
    ) {
        log.info(problem);
        List<Domino> dominoes = createDomino(problem);
        SMT2 smt2 = DominoSolve.createSMT2FromDomino(dominoes);

        Status check = SMTUtils.check(smt2);
        return ResponseEntity.ok().body(check.toString());
    }

    @Operation(description = "Модель решения проблемы соответствия Поста")
    @PostMapping(value = "/modelSolutionsProblemsPostCompliance")
    public ResponseEntity<String> getModel(
            @Parameter(description = "problem")
            @RequestBody String problem
    ) {
        log.info(problem);
        List<Domino> dominoes = createDomino(problem);
        SMT2 smt2 = DominoSolve.createSMT2FromDomino(dominoes);

        Model model = SMTUtils.getModel(smt2);
        String string = model.toString();
        String[] split = string.split("\\)\n");
        List<String> list = Arrays.stream(split).sorted().toList();
        String join = String.join(")\n", list);
        return ResponseEntity.ok().body(join);
    }

    private List<Domino> createDomino(String problem) {
        List<Domino> dominoes = new ArrayList<>();
        List<String> dominoStrings = List.of(problem.split("\n"));
        for (String domineString : dominoStrings) {
            dominoes.add(new Domino(domineString));
        }
        return dominoes;
    }
}
