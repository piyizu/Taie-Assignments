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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.Comparator;
import java.util.LinkedList;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    private void getReachableStmts(Stmt cur, CFG<Stmt> cfg, LinkedList<Stmt> stmtVisited, LinkedList<Edge> badEdges) {
        if(stmtVisited.contains(cur) ) {
            return;
        }
        stmtVisited.add(cur);
        for( Edge<?> e : cfg.getOutEdgesOf(cur) ) {
            if( !badEdges.contains(e) ) {
                getReachableStmts((Stmt) e.getTarget(), cfg, stmtVisited, badEdges);
            }
        }
    }
    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // done - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        LinkedList<Edge> badEdges = new LinkedList<Edge>();

        // dead branch FIRST - eliminate BAD EDGES
        for(Stmt s : cfg.getNodes() ) {
            if(s instanceof If ifBranch) {
                Value val = ConstantPropagation.evaluate(ifBranch.getCondition(), constants.getInFact(ifBranch));
                if(val.isConstant() ) {
                    int vConst = val.getConstant();
                    for(Edge<?> e : cfg.getOutEdgesOf(ifBranch) ) {
                        if(vConst == 1 && e.getKind() == Edge.Kind.IF_FALSE) {
                            badEdges.add(e);
                        }
                        else if(vConst == 0 && e.getKind() == Edge.Kind.IF_TRUE) {
                            badEdges.add(e);
                        }
                    }
                }
            }
            else if(s instanceof SwitchStmt switchBranch) {
                Value val = constants.getInFact(switchBranch).get(switchBranch.getVar() );
                if( val.isConstant() ) {
                    int vConst = val.getConstant();
                    if(switchBranch.getCaseValues().contains(vConst) ) { // some case is not dead
                        for(Edge<?> e : cfg.getOutEdgesOf(switchBranch) ) {
                            if(e.getKind() == Edge.Kind.SWITCH_DEFAULT
                               || (e.getKind() == Edge.Kind.SWITCH_CASE
                                   && e.getCaseValue() != vConst) ) {
                                badEdges.add(e);
                            }
                        }
                    }
                    else {
                        for(Edge<?> e : cfg.getOutEdgesOf(switchBranch) ) { // all cases except for default are dead
                            if(e.getKind() == Edge.Kind.SWITCH_CASE) {
                                badEdges.add(e);
                            }
                        }
                    }
                }
            }
        }

        // control flow unreachable - get RELATIVELY reachable statements
        LinkedList<Stmt> reachableStmts = new LinkedList<Stmt>();
        getReachableStmts(cfg.getEntry(), cfg, reachableStmts, badEdges);
        for(Stmt s : cfg.getNodes() ) {
            if(!reachableStmts.contains(s) && !cfg.isExit(s) ) { // Exit Node excluded
                deadCode.add(s);
            }
        }

        // dead assignment - eliminate non-side-effective dead assignments
        for(Stmt s : reachableStmts) {
            if(s instanceof AssignStmt<?,?> assign) {
                if( assign.getLValue() instanceof Var v
                    && !liveVars.getOutFact(assign).contains(v)
                    && hasNoSideEffect(assign.getRValue() ) ) {
                    deadCode.add(s);
                }
            }
        }

        return deadCode;
    }

    // Erh.... I realise that I did not consider many more cases when I see this...f**king good method
    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
