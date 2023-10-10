package ru.bmstu.iu9.tfl_lab_1.model.rest;

import io.swagger.v3.oas.annotations.media.Schema;
import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;

@Schema
@Getter
@Setter
@AllArgsConstructor
@NoArgsConstructor
public class SrsStringsArbitrary {
    @Schema(description = "Произвольные TRS строки", example = "ff->f\nf->ff")
    private String srsStrings;
}
