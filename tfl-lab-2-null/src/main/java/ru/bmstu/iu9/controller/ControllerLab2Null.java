package ru.bmstu.iu9.controller;

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
import ru.bmstu.iu9.tfl_lab_lib.model.Regex;
import ru.bmstu.iu9.tfl_lab_lib.model.automaton.NFA;
import ru.bmstu.iu9.tfl_lab_lib.utils.Converter;

@Slf4j
@Tag(name = "Lab2-null", description = "Lab 2-null description")
@RestController
@RequestMapping("/rest/lab-2-null")
@RequiredArgsConstructor
public class ControllerLab2Null {
    @Operation(description = "Конвертация автомата в регулярку")
    @PostMapping(value = "/convertArbitraryToStandard")
    public ResponseEntity<String> convert(
            @Parameter(description = "Автомат")
            @RequestBody String automate
    ) {
        log.info(automate);
        NFA nfa = Converter.convertStringAutomateToNFA(automate);
        Regex regex = Converter.convertNFAToRegex(nfa);
        return ResponseEntity.ok().body(regex.toString());
    }
}
