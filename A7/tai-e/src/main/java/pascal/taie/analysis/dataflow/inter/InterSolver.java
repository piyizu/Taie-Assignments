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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;

import java.util.*;

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

    public Fact FetchConstantPropagationFactsInExternalProcedure(Node node) {
        // The alias-aware analyser says, mayday! we cannot fetch the facts in other procedures!
        // And now it is our time to help the poor and little aa analyser!

        return result.getInFact(node); // return the in-fact of the node, which the aa analyser needs

    }

    private void initialize() {
        // finish me
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
        workList = new LinkedList<>();
        workList.addAll(icfg.getNodes() );
        InterConstantPropagation icpanalysis = (InterConstantPropagation)analysis;
        while(!workList.isEmpty() ) {
            Node curNode = workList.remove();
            for(ICFGEdge<Node> inEdge : icfg.getInEdgesOf(curNode) ) {
                analysis.meetInto(
                        analysis.transferEdge(inEdge, result.getOutFact(inEdge.getSource() ) ),
                        result.getInFact(curNode) );
            }
            if(analysis.transferNode(curNode, result.getInFact(curNode), result.getOutFact(curNode) ) ) {
                for(Node suc : icfg.getSuccsOf(curNode) ) {
                    if(!workList.contains(suc) ) {
                        workList.add(suc);
                    }
                }
                /*if(curNode instanceof StoreArray || curNode instanceof StoreField ) {
                    for(Node n : icfg.getNodes() ) {
                        if(n instanceof LoadArray || n instanceof LoadField) {
                            if(!workList.contains(n) ) {
                                workList.add(n);
                            }
                        }
                    }
                }*/
                if(curNode instanceof StoreArray sta) {
                    Collection<?> aliasSet = icpanalysis.FetchAliasVarSetForVar(sta.getArrayAccess().getBase() );
                    for(Node n : icfg) {
                        if(n instanceof LoadArray lan) {
                            if( aliasSet.contains(lan.getArrayAccess().getBase() ) && !workList.contains(n) ) {
                                workList.add(n);
                            }
                        }
                    }
                }
                if(curNode instanceof StoreField stf) {
                    JField field = stf.getFieldRef().resolve();
                    if(stf.isStatic() ) {
                        for(Node n : icfg) {
                            if(n instanceof  LoadField ldf
                                    && ldf.isStatic()
                                    && ldf.getFieldRef().resolve().equals(field)
                                    && !workList.contains(n) ) {
                                workList.add(n);
                            }
                        }
                    }
                    else {
                        InstanceFieldAccess itfa = (InstanceFieldAccess)stf.getFieldAccess();
                        Collection<?> aliasSet = icpanalysis.FetchAliasVarSetForVar(itfa.getBase() );
                        for(Node n : icfg) {
                            if(n instanceof LoadField ldf
                                    && ldf.getFieldAccess() instanceof InstanceFieldAccess ldfitfa
                                    && aliasSet.contains(ldfitfa.getBase())
                                    && ldf.getFieldRef().resolve().equals(field)
                                    && !workList.contains(n) ) {
                                workList.add(n);
                            }
                        }
                    }
                }
            }
        }
    }
}
