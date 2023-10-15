package ru.bmstu.iu9.tfl_lab_2.service;

import lombok.extern.slf4j.Slf4j;
import org.apache.commons.lang3.SerializationUtils;
import org.springframework.stereotype.Service;
import ru.bmstu.iu9.tfl_lab_2.model.parser.Tree;
import ru.bmstu.iu9.tfl_lab_2.utils.ACI;
import ru.bmstu.iu9.tfl_lab_2.utils.DSTR;
import ru.bmstu.iu9.tfl_lab_2.utils.Parser;
import ru.bmstu.iu9.tfl_lab_2.utils.SSNF;

@Slf4j
@Service
public class OptimizationService {
    public String optimization(String regex) {
//        Tree tree = Parser.parser("(((a|c|(a|b)c|c|(a|b)c|c|a(b|c)|a|b|a)|b)*|((acd)e)*)*");
//                Tree tree = parser.parser("(A|B)C)");
        Tree tree = Parser.parser(regex);
        log.info(Tree.drawTree(tree));
        log.info(tree.toString());
        Tree ssnfTree = SSNF.ssnf(SerializationUtils.clone(tree));
        log.info(Tree.drawTree(ssnfTree));
        log.info(ssnfTree.toString());
        Tree associativityTree = ACI.normalizeAssociativity(SerializationUtils.clone(ssnfTree));
        log.info(Tree.drawTree(associativityTree));
        log.info(associativityTree.toString());
        Tree commutativityTree = ACI.normalizeCommutativity(SerializationUtils.clone(associativityTree));
        log.info(Tree.drawTree(commutativityTree));
        log.info(commutativityTree.toString());
        Tree idempotencyTree = ACI.normalizeIdempotency(SerializationUtils.clone(commutativityTree));
        log.info(Tree.drawTree(idempotencyTree));
        log.info(idempotencyTree.toString());
        Tree dstrTree = DSTR.dstrTree(idempotencyTree);
        log.info(Tree.drawTree(dstrTree));
        log.info(dstrTree.toString());
        Tree commutativity = ACI.normalizeCommutativity(idempotencyTree);
        log.info(Tree.drawTree(commutativity));
        log.info(commutativity.toString());
        return commutativity.toString();
    }
}
