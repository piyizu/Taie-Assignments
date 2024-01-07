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

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    private void getWorkListDFS(Node cur, CFG<Node> cfg, Queue<Node> workList) {
        if(workList.contains(cur)) {
            return;
        }
        workList.add(cur);
        for(Node next : (analysis.isForward() ? cfg.getSuccsOf(cur) : cfg.getPredsOf(cur) ) ) {
            getWorkListDFS(next, cfg, workList);
        }
    }
    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODOO - finish me
        initializeForward(cfg, result);

        Queue<Node> workList = new LinkedList<Node>();
        getWorkListDFS(cfg.getEntry(), cfg, workList);
        for(Node n : cfg.getNodes() ) {
            getWorkListDFS(n, cfg, workList);
        }

        while(!workList.isEmpty() ) {
            Node p = workList.remove();
            for(Node pre : cfg.getPredsOf(p) ) {
                analysis.meetInto(result.getOutFact(pre), result.getInFact(p) );
            }
            if(analysis.transferNode(p, result.getInFact(p), result.getOutFact(p) ) ) {
                for(Node suc : cfg.getSuccsOf(p) ) {
                    if(!workList.contains(suc) ) {
                        workList.add(suc);
                    }
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODOO - finish me

        initializeBackward(cfg, result);

        Queue<Node> workList = new LinkedList<Node>();
        getWorkListDFS(cfg.getExit(), cfg, workList);
        for(Node n : cfg.getNodes() ) {
            getWorkListDFS(n, cfg, workList);
        }

        while(!workList.isEmpty() ) {
            Node p = workList.remove();
            for(Node suc : cfg.getSuccsOf(p) ) {
                analysis.meetInto(result.getInFact(suc), result.getOutFact(p) );
            }

            if(analysis.transferNode(p, result.getInFact(p), result.getOutFact(p) ) ) {
                for(Node pre : cfg.getPredsOf(p) ) {
                    if(!workList.contains(pre) ) {
                        workList.add(pre);
                    }
                }
            }
        }
    }
}
