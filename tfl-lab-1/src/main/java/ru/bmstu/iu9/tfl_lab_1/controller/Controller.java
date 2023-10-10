package ru.bmstu.iu9.tfl_lab_1.controller;

import io.swagger.v3.oas.annotations.Operation;
import io.swagger.v3.oas.annotations.Parameter;
import io.swagger.v3.oas.annotations.tags.Tag;
import lombok.NonNull;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import ru.bmstu.iu9.tfl_lab_1.model.rest.SrsString;
import ru.bmstu.iu9.tfl_lab_1.model.rest.SrsStringsArbitrary;
import ru.bmstu.iu9.tfl_lab_1.model.smt.SMT2;
import ru.bmstu.iu9.tfl_lab_1.service.SMTService;
import java.util.ArrayList;
import java.util.List;

@Slf4j
@Tag(name = "Lab1", description = "Lab 1 description")
@RestController
@RequestMapping("/rest/lab-1")
@RequiredArgsConstructor
public class Controller {
    @NonNull
    private final SMTService smtService;

    @Operation(description = "Конвертация произвольной строки, содержащей в себе SRS правила в " +
            "массив объектов SrsString")
    @PostMapping(value = "/convertArbitraryToStandard")
    public ResponseEntity<List<SrsString>> convert(
            @Parameter(description = "SRS правило (произвольное)")
            @RequestBody SrsStringsArbitrary srsStringsArbitrary
    ) {
        String[] split = srsStringsArbitrary.getSrsStrings().split("\n");
        List<SrsString> srsStrings = new ArrayList<>();
        for (String s : split) {
            srsStrings.add(new SrsString(s));
        }
        return ResponseEntity.ok().body(srsStrings);
    }

    @Operation(description = "Проверка завершаемости SRS посредством построения оценки линейных " +
            "операторах размерности 2 над арктическим полукольцом.")
    @PostMapping(value = "/isSatisfiable")
    public ResponseEntity<String> create(
            @Parameter(description = "SRS правило")
            @RequestBody List<SrsString> srsStrings
    ) {
        SMT2 smt2 = smtService.generateFileSMT2(srsStrings);
        log.debug(smt2.toString());
        String test = smtService.smtGen(smt2.toString());
        return ResponseEntity.ok().body(test);
    }
}
