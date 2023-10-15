package ru.bmstu.iu9.tfl_lab_2.controller;

import io.swagger.v3.oas.annotations.Operation;
import io.swagger.v3.oas.annotations.tags.Tag;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import ru.bmstu.iu9.tfl_lab_2.service.OptimizationService;

@Slf4j
@Tag(name = "Lab2", description = "Lab 2 description")
@RestController
@RequestMapping("/rest/lab-2")
@RequiredArgsConstructor
public class CController {
    private final OptimizationService optimizationService;

    @Operation(description = "")
    @PostMapping(value = "/ss")
    public ResponseEntity<String> create(String regex) {
        String optimizationRegex = optimizationService.optimization(regex);
        return ResponseEntity.ok().body(optimizationRegex);
    }
}