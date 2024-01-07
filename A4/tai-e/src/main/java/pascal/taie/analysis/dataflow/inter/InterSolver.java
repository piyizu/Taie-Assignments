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

package pascal.taie.analysis.dataflow.inter;

import heros.flowfunc.Transfer;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Return;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        //  - finish me
        for(Node n : icfg) {
            result.setInFact(n, analysis.newInitialFact() );
            result.setOutFact(n, analysis.newInitialFact() );
        }

        icfg.entryMethods().forEach((method) -> {
            Node entry = icfg.getEntryOf(method);
            result.setOutFact(entry, analysis.newBoundaryFact(entry) );
        });

    }

    private void doSolve() {
        //  - finish me
        Queue<Node> workList = new LinkedList<>();

        for(Node n : icfg) {
            workList.add(n);
        }

        while (!workList.isEmpty() ) {
            Node b = workList.remove();
            for(ICFGEdge<Node> e : icfg.getInEdgesOf(b) ) {
                analysis.meetInto(
                        analysis.transferEdge(e, result.getOutFact((Node) e.getSource()) ),
                        result.getInFact(b) );
            }

            if( analysis.transferNode(b, result.getInFact(b), result.getOutFact(b) ) ) {
                for(Node n : icfg.getSuccsOf(b) ) { // call edges and return edges are covered
                    if(!workList.contains(n) ) {
                        workList.add(n);
                    }
                }
            }
        }
    }
}
