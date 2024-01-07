/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.Analysis;
import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // done - finish me
        initializeForward(cfg, result);

        // The following initialisation code can be replaced by
        //Queue<Node> workList = new LinkedList<>(cfg.getNodes());
        Queue<Node> workList = new LinkedList<>();
        for(Node n : cfg.getNodes() ) {
            initWorkListDFS(cfg, cfg.getEntry(), workList);
        }

        while(!workList.isEmpty()) {
            Node currentNode = workList.remove();
            // if(cfg.isEntry(currentNode)) continue;
            for(Node n : cfg.getPredsOf(currentNode)) {
                analysis.meetInto(result.getOutFact(n), result.getInFact(currentNode));
            }
            if( analysis.transferNode(
                    currentNode,
                    result.getInFact(currentNode),
                    result.getOutFact(currentNode) ) ) {
                for(Node n : cfg.getSuccsOf(currentNode) ) {
                    if(!workList.contains(n)) {
                        workList.add(n);
                    }
                }
            }
        }
    }

    private void initWorkListDFS(CFG<Node> cfg, Node curNode, Queue<Node> workList) {
        if(workList.contains(curNode) ) {
            return;
        }

        workList.add(curNode);
        for(Node s : cfg.getSuccsOf(curNode) ) {
            if(!workList.contains(s) ) {
                initWorkListDFS(cfg, s, workList);
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
