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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private Set<Stmt> stmtSet = new HashSet<Stmt>();

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();

        stmtSet.clear();

        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        //  finish me
        if(callGraph.addReachableMethod(csMethod) ) {  // if the csmethod has not been added, then do something
            List<Stmt> methodStmts = csMethod.getMethod().getIR().getStmts();
            stmtSet.addAll(methodStmts);
            for(Stmt stmt : methodStmts) {
                if(stmt instanceof New snew) {
                    Obj newObj = heapModel.getObj(snew);
                    Context objContext = contextSelector.selectHeapContext(csMethod, newObj);
                    workList.addEntry(
                            csManager.getCSVar(csMethod.getContext(), snew.getLValue() ),
                            PointsToSetFactory.make( csManager.getCSObj(objContext, newObj) )
                    );
                }
                else if(stmt instanceof Copy cp) {
                    addPFGEdge(
                            csManager.getCSVar(csMethod.getContext(), cp.getRValue() ),
                            csManager.getCSVar(csMethod.getContext(), cp.getLValue() )
                    );
                }
                else if(stmt instanceof StoreField stfd && stfd.isStatic() ) { //c:var-->T.f
                    JField field = stfd.getFieldAccess().getFieldRef().resolve();
                    addPFGEdge(
                            csManager.getCSVar(csMethod.getContext(), stfd.getRValue() ),
                            csManager.getStaticField(field)
                    );
                }
                else if(stmt instanceof LoadField ldfd && ldfd.isStatic() ) {  //T.f--->c:var
                    JField field = ldfd.getFieldAccess().getFieldRef().resolve();
                    addPFGEdge(
                            csManager.getStaticField(field),
                            csManager.getCSVar(csMethod.getContext(), ldfd.getLValue() )
                    );
                }
                else if(stmt instanceof Invoke ivk && ivk.isStatic() ) {
                    JMethod callee = ivk.getMethodRef().resolve();
                    CSCallSite csCallSite = csManager.getCSCallSite(csMethod.getContext(), ivk);
                    Context newContext = contextSelector.selectContext(csCallSite, callee);
                    CSMethod csCallee = csManager.getCSMethod(newContext, callee);
                    if(callGraph.addEdge(
                            new Edge<CSCallSite, CSMethod>(
                                    CallKind.STATIC,
                                    csCallSite,
                                    csCallee) ) ) { // if the call edge has not been added then do something
                        addReachable(csCallee);  // add the callee to the reachable methods
                        int paramCount = callee.getParamCount();
                        for(int i = 0; i < paramCount; ++i) {
                            addPFGEdge(
                                    csManager.getCSVar(csMethod.getContext(), ivk.getInvokeExp().getArg(i) ),
                                    csManager.getCSVar(newContext, callee.getIR().getParam(i) )
                            );
                        }
                        if(ivk.getDef().isPresent() ) { // only add return edges when there is a receiving variable
                            for(Var retVar : callee.getIR().getReturnVars() ) {
                                addPFGEdge(
                                        csManager.getCSVar(newContext, retVar),
                                        csManager.getCSVar(csMethod.getContext(), ivk.getLValue() )
                                );
                            }
                        }
                    }
                }
                else {
                    continue;
                }
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // - finish me
        if(pointerFlowGraph.addEdge(source, target) ) {
            if(!source.getPointsToSet().isEmpty() ) {
                workList.addEntry( // trigger the propagation
                        target,
                        source.getPointsToSet()
                );
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        //  finish me
        while(!workList.isEmpty() ) {
            WorkList.Entry pair = workList.pollEntry();
            Pointer n = pair.pointer();
            PointsToSet pts = pair.pointsToSet();
            PointsToSet delta = PointsToSetFactory.make();
            for(CSObj obj : pts) {
                if(!n.getPointsToSet().contains(obj) ) {
                    delta.addObject(obj);
                }
            }
            if(!delta.isEmpty() ) {
                propagate(n, delta);
                if(n instanceof CSVar x) {
                    for(CSObj csObj : delta) {
                        for(Stmt s : stmtSet) {
                            if(s instanceof LoadField ldfd
                                    && !ldfd.isStatic()
                                    && ldfd.getFieldAccess() instanceof InstanceFieldAccess itsfa
                                    && itsfa.getBase().equals(x.getVar() ) ) { // y = "x".f
                                JField field = itsfa.getFieldRef().resolve();
                                addPFGEdge(
                                        csManager.getInstanceField(csObj, field),
                                        csManager.getCSVar(x.getContext(), ldfd.getLValue() )
                                        // the context of y is that of x
                                );
                            }
                            else if(s instanceof StoreField stfd
                                    && !stfd.isStatic()
                                    && stfd.getFieldAccess() instanceof InstanceFieldAccess itsfa
                                    && itsfa.getBase().equals(x.getVar() ) ) {  // "x".f = y
                                JField field = itsfa.getFieldRef().resolve();
                                addPFGEdge(
                                        csManager.getCSVar(x.getContext(), stfd.getRValue() ),
                                        csManager.getInstanceField(csObj, field)
                                );
                            }
                            else if(s instanceof LoadArray ldar
                                    && ldar.getArrayAccess().getBase().equals(x.getVar() ) ) {  // y = "x"[...]
                                addPFGEdge(
                                        csManager.getArrayIndex(csObj),
                                        csManager.getCSVar(x.getContext(), ldar.getLValue() )
                                );
                            }
                            else if(s instanceof StoreArray star
                                    && star.getArrayAccess().getBase().equals(x.getVar() ) ) { // "x"[...] = y
                                addPFGEdge(
                                        csManager.getCSVar(x.getContext(), star.getRValue() ),
                                        csManager.getArrayIndex(csObj)
                                );
                            }
                        }
                        processCall(x, csObj);
                    }
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // finish me
        // return null;
        if(!pointsToSet.isEmpty() ) {
            pointer.getPointsToSet().addAll(pointsToSet);
            for(Pointer successor : pointerFlowGraph.getSuccsOf(pointer) ) {
                workList.addEntry(successor, pointsToSet); // to only propagate new points-to relations is OK
            }
        }
        return pointer.getPointsToSet();
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        //  finish me
        Set<Invoke> invokesToConcern = new HashSet<>();
        for(Stmt s : stmtSet) {
            if(s instanceof Invoke ivk
                    && ivk.getInvokeExp() instanceof InvokeInstanceExp ivkist
                    && ivkist.getBase().equals(recv.getVar() ) ) {
                invokesToConcern.add(ivk);
            }
        }

        for(Invoke ivk : invokesToConcern) {
            JMethod callee = resolveCallee(recvObj, ivk);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), ivk);
            Context newContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(newContext, callee);

            // add recvObj to c^t:m_this
            workList.addEntry(
                    csManager.getCSVar(newContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );

            if(callGraph.addEdge(
                    new Edge<CSCallSite, CSMethod>(
                            getCallKind(ivk),
                            csCallSite,
                            csCallee
                    ) ) ) { // if the call edge has not been added then do something
                addReachable(csCallee);
                int paramCount = callee.getParamCount();
                for(int i = 0; i < paramCount; ++i) {
                    addPFGEdge(  ///////// be CAREFUL that IDEA may provide you with unexpected auto completions
                            csManager.getCSVar(recv.getContext(), ivk.getInvokeExp().getArg(i) ),
                            csManager.getCSVar(newContext, callee.getIR().getParam(i) )
                    );
                }
                if(ivk.getDef().isPresent() ) {
                    for(Var retVar : callee.getIR().getReturnVars() ) {
                        addPFGEdge(
                                csManager.getCSVar(newContext, retVar),
                                csManager.getCSVar(recv.getContext(), ivk.getLValue() )
                        );
                    }
                }
            }
        }
    }

    private static CallKind getCallKind(Invoke callSite) {
        if(callSite.isStatic() ) return CallKind.STATIC;
        else if(callSite.isInterface() ) return CallKind.INTERFACE;
        else if(callSite.isVirtual() ) return CallKind.VIRTUAL;
        else if(callSite.isSpecial() ) return CallKind.SPECIAL;
        else if(callSite.isDynamic() ) return CallKind.DYNAMIC;
        else {
            throw new AnalysisException("No available callkind");
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
