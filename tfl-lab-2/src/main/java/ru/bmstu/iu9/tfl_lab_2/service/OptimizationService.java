package ru.bmstu.iu9.tfl_lab_2.service;

import lombok.extern.slf4j.Slf4j;
import org.apache.commons.lang3.SerializationUtils;
import org.springframework.stereotype.Service;
import ru.bmstu.iu9.tfl_lab_2.model.Tree;
import ru.bmstu.iu9.tfl_lab_2.utils.ACI;
import ru.bmstu.iu9.tfl_lab_2.utils.DSTR;
import ru.bmstu.iu9.tfl_lab_2.utils.Parser;
import ru.bmstu.iu9.tfl_lab_2.utils.SSNF;

@Slf4j
@Service
public class OptimizationService {
    public String optimization(String regex) {
        Tree tree = Parser.parser(regex);
        log.debug(Tree.drawTree(tree));
        log.debug(tree.toString());
        Tree ssnfTree = SSNF.ssnf(SerializationUtils.clone(tree));
        log.debug(Tree.drawTree(ssnfTree));
        log.debug(ssnfTree.toString());
        Tree associativityTree = ACI.normalizeAssociativity(SerializationUtils.clone(ssnfTree));
        log.debug(Tree.drawTree(associativityTree));
        log.debug(associativityTree.toString());
        Tree commutativityTree = ACI.normalizeCommutativity(SerializationUtils.clone(associativityTree));
        log.debug(Tree.drawTree(commutativityTree));
        log.debug(commutativityTree.toString());
        Tree dstrTree = DSTR.dstrTree(SerializationUtils.clone(commutativityTree));
        log.debug(Tree.drawTree(dstrTree));
        log.debug(dstrTree.toString());
        Tree idempotency = ACI.normalizeIdempotency(SerializationUtils.clone(dstrTree));
        log.debug(Tree.drawTree(idempotency));
        log.debug(idempotency.toString());
        return idempotency.toString();
    }
}
