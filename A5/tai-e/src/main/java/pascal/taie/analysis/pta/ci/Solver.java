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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    private static Set<Stmt> stmtSet = new HashSet<>();

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        stmtSet.clear(); // clear the stmts set
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        //  finish me
        if(!callGraph.reachableMethods().toList().contains(method) ) {
            callGraph.addReachableMethod(method);
            stmtSet.addAll(method.getIR().getStmts()); //add this statement to S
            method.getIR().forEach((Stmt stmt) -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        //  - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(stmt.getLValue() ),
                    new PointsToSet(heapModel.getObj(stmt))
            );
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue() ),
                    pointerFlowGraph.getVarPtr(stmt.getLValue() )
            );
            return null;
        }

        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if(field.isStatic() ) {
                addPFGEdge(
                        pointerFlowGraph.getStaticField(field),
                        pointerFlowGraph.getVarPtr(stmt.getLValue() )
                );
            }
            return null;
        }

        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if(field.isStatic() ) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue() ),
                        pointerFlowGraph.getStaticField(field)
                );
            }
            return null;
        }

        public Void visit(Invoke stmt) {
            if(stmt.isStatic() ) {
                JMethod method = hierarchy.dispatch(
                        stmt.getMethodRef().getDeclaringClass(),
                        stmt.getMethodRef()
                );
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method)) ) { // add a call edge
                    addReachable(method); // add reachable method
                    int paramNum = method.getParamCount();
                    for(int i = 0; i < paramNum; ++i ) { // arguments to parameters
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i) ),
                                pointerFlowGraph.getVarPtr(method.getIR().getParam(i) )
                        );
                    }
                    if(stmt.getDef().isPresent()) {
                        for(Var returnVar : method.getIR().getReturnVars() ) { // return variables to target
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(returnVar),
                                    pointerFlowGraph.getVarPtr(stmt.getLValue() )
                            );
                        }
                    }
                }
            }

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // - finish me
        if( pointerFlowGraph.addEdge(source, target) ) {
            if(!source.getPointsToSet().isEmpty() ) {
                workList.addEntry(target, source.getPointsToSet() );
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        //  - finish me
        while(!workList.isEmpty() ) {
            WorkList.Entry cur = workList.pollEntry();
            PointsToSet delta = new PointsToSet();
            for(Obj obj : cur.pointsToSet() ) { // delta = pts - pt(n)
                if(!cur.pointer().getPointsToSet().contains(obj) ) {
                    delta.addObject(obj);
                }
            }
            if(delta.isEmpty()) continue;
            propagate(cur.pointer(), delta);
            if(cur.pointer() instanceof VarPtr vp) {
                for(Obj obj : delta) {
                    for(Stmt stmt : stmtSet) {
                        // remember to manipulate statements related only to vp.getVar()
                        // remember to filter vp.getVar() == base instead of other vars!!
                        if(stmt instanceof LoadField s
                                && s.getFieldAccess() instanceof InstanceFieldAccess sifa
                                && vp.getVar().equals(sifa.getBase()) ) {
                            JField field = s.getFieldRef().resolve();
                            addPFGEdge(
                                    pointerFlowGraph.getInstanceField(obj, field),
                                    pointerFlowGraph.getVarPtr(s.getLValue() )
                            );
                        }
                        else if(stmt instanceof StoreField s
                                && s.getFieldAccess() instanceof InstanceFieldAccess sifa
                                && vp.getVar().equals(sifa.getBase()) ) {
                            JField field = s.getFieldRef().resolve();
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(s.getRValue() ),
                                    pointerFlowGraph.getInstanceField(obj, field)
                            );
                        }
                        // be careful of what pointer we are manipulating now!!!
                        // vp.getVar() == array pointer, not the source or target
                        else if(stmt instanceof StoreArray s && vp.getVar().equals(s.getArrayAccess().getBase())) {
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(s.getRValue() ),
                                    pointerFlowGraph.getArrayIndex(obj)
                            );
                        }
                        else if(stmt instanceof LoadArray s && vp.getVar().equals(s.getArrayAccess().getBase())) {
                            addPFGEdge(
                                    pointerFlowGraph.getArrayIndex(obj),
                                    pointerFlowGraph.getVarPtr(s.getLValue() )
                            );

                        }
                    }
                    processCall(vp.getVar(), obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        //  - finish me
        //return null;
        if(!pointsToSet.isEmpty() ) {
            for(Obj obj : pointsToSet) {
                pointer.getPointsToSet().addObject(obj);
            }
            for(Pointer successorPointer : pointerFlowGraph.getSuccsOf(pointer) ) {
                workList.addEntry(successorPointer, pointer.getPointsToSet() );
            }
        }

        return pointer.getPointsToSet();
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        //  - finish me
        Set<Stmt> stmtsToConcern = new HashSet<>();

        for(Stmt stmt : stmtSet) { // this sucks! You CANNOT modify the set while for-each statements are being executed!
            if(stmt instanceof Invoke s
                    && s.getInvokeExp() instanceof InvokeInstanceExp sivkexp
                    && sivkexp.getBase().equals(var) ) {
                stmtsToConcern.add(stmt);
            }
        }

        for(Stmt stmt : stmtsToConcern) {
            Invoke s = (Invoke) stmt;
            JMethod callee = resolveCallee(recv, s);
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(callee.getIR().getThis()),
                    new PointsToSet(recv)
            );
            CallKind callKind = getCallKind(s);
            if(callGraph.addEdge(new Edge<>(callKind, s, callee))) {
                addReachable(callee);
                int paramNum = callee.getParamCount();
                for(int i = 0; i < paramNum; ++i) { // arguments -> parameters
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(s.getInvokeExp().getArg(i)),
                            pointerFlowGraph.getVarPtr(callee.getIR().getParam(i))
                    );
                }
                if(s.getDef().isPresent()) {
                    for(Var returnVar : callee.getIR().getReturnVars()) { // return variables -> target
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(returnVar),
                                pointerFlowGraph.getVarPtr(s.getLValue())
                        );
                    }
                }
            }
        }
    }

    private CallKind getCallKind(Invoke invoke) {
        if(invoke.isDynamic()) return CallKind.DYNAMIC;
        else if(invoke.isStatic()) return CallKind.STATIC;
        else if(invoke.isSpecial()) return CallKind.SPECIAL;
        else if(invoke.isVirtual()) return CallKind.VIRTUAL;
        else if(invoke.isInterface()) return CallKind.INTERFACE;
        else return null;
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
