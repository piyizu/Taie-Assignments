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
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Pair;

import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
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
        // finish me
        if(callGraph.addReachableMethod(csMethod) ) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for(Stmt s : csMethod.getMethod().getIR().getStmts() ) {
                s.accept(stmtProcessor); //manipulate statements in StmtProcessor
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

        //  if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New newStmt) { // x = new ...
            Obj newObj = heapModel.getObj(newStmt);
            Context newHeapContext = contextSelector.selectHeapContext(csMethod, newObj);
            CSObj newCSObj = csManager.getCSObj(newHeapContext, newObj); // this is the cs object in the PTS
            workList.addEntry(
                    csManager.getCSVar(csMethod.getContext(), newStmt.getLValue() ),
                    PointsToSetFactory.make(newCSObj)
            );
            return null;
        }

        public Void visit(Copy copyStmt) { // x = y
            addPFGEdge( // do not forget to use addPFGEdge where we may need to add something to the worklist
                    csManager.getCSVar(csMethod.getContext(), copyStmt.getRValue() ),
                    csManager.getCSVar(csMethod.getContext(), copyStmt.getLValue() )
            );
            return null;
        }

        public Void visit(LoadField ldf) { // x = T.f
            if(ldf.isStatic() ) {
                addPFGEdge(
                        csManager.getStaticField(ldf.getFieldRef().resolve() ),
                        csManager.getCSVar(csMethod.getContext(), ldf.getLValue() )
                );
            }
            return null;
        }

        public Void visit(StoreField stf) { // T.f = y
            if(stf.isStatic() ) {
                addPFGEdge(
                        csManager.getCSVar(csMethod.getContext(), stf.getRValue() ),
                        csManager.getStaticField(stf.getFieldRef().resolve() )
                );
            }
            return null;
        }

        public Void visit(Invoke invoke) { // x = T.m(...)
            if(invoke.isStatic() ) {
                CSCallSite csCallSite = csManager.getCSCallSite(csMethod.getContext(), invoke);
                JMethod callee = invoke.getInvokeExp().getMethodRef().resolve();
                Context staticInvokeContext = contextSelector.selectContext(csCallSite, callee );
                CSMethod csCallee = csManager.getCSMethod(staticInvokeContext, callee);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee) ) ) {
                    addReachable(csCallee);
                    int paramCount = callee.getParamCount();
                    for(int i = 0; i < paramCount; ++i) {
                        addPFGEdge(
                                csManager.getCSVar(csMethod.getContext(), invoke.getInvokeExp().getArg(i) ),
                                csManager.getCSVar(csCallee.getContext(), callee.getIR().getParam(i) )
                        );
                    }
                    if(invoke.getResult() != null) {
                        for (Var retVar : callee.getIR().getReturnVars()) {
                            addPFGEdge(
                                    csManager.getCSVar(csCallee.getContext(), retVar),
                                    csManager.getCSVar(csMethod.getContext(), invoke.getResult())
                            );
                        }

                        // if this callee is a source
                        CSObj csTaintObject = taintAnalysis.makeTaintObject(invoke, callee, csMethod);
                        if(csTaintObject != null) {
                            workList.addEntry(
                                    csManager.getCSVar(csMethod.getContext(), invoke.getResult() ),
                                    PointsToSetFactory.make(csTaintObject)
                            );
                        }
                    }

                    // manipulate taint transfers
                    Set<Pair<Pointer, Pair<Pointer, Type> > > edges = taintAnalysis.analyseTaintFlowEdges(csCallSite, csCallee);
                    addTaintFGEdges(edges);

                    // record taint sink sites
                    Set<Integer> indexes = taintAnalysis.getTaintSinkIndex(callee);
                    if(!indexes.isEmpty() ) {
                        for(Integer index : indexes) {
                            taintAnalysis.addTaintSinkSite(csCallSite, index);
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
        // finish me
        if(pointerFlowGraph.addEdge(source, target) ) {
            if(!source.getPointsToSet().isEmpty() ) {
                workList.addEntry(target, source.getPointsToSet() );
            }
        }
    }

    private void addTaintFGEdges(Set<Pair<Pointer, Pair<Pointer, Type> > > edgesToAdd) {
        if(!edgesToAdd.isEmpty() ) {
            for(Pair<Pointer, Pair<Pointer, Type> > edge : edgesToAdd) {
                Pointer source = edge.first();
                Pointer target = edge.second().first();
                Type targetType = edge.second().second();
                if(taintAnalysis.getTaintFlowGraph().addTaintFGEdge(source, target, targetType) ) {
                    /*if(!source.getPointsToSet().isEmpty() ) {  // THIS IS IMPORTANT!
                        workList.addEntry(target, source.getPointsToSet() );
                    } <---------------WRONG CODE*/
                    // DO NOT ADD NORMAL ABSTRACT OBJECTS TO TAINT TARGETS!
                    if(!source.getPointsToSet().isEmpty() ) {
                        PointsToSet taintObjectsToPropagate = PointsToSetFactory.make();
                        for(CSObj csObj : source.getPointsToSet() ) {
                            if(taintAnalysis.isObjectTaint(csObj.getObject() ) ) {
                                taintObjectsToPropagate.addObject(csObj);
                            }
                        }
                        if(!taintObjectsToPropagate.isEmpty() ) {
                            workList.addEntry(target, taintObjectsToPropagate);
                        }
                    }
                }
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // finish me
        while(!workList.isEmpty() ) {
            WorkList.Entry n = workList.pollEntry();
            Pointer p = n.pointer();
            PointsToSet pts = n.pointsToSet();
            PointsToSet delta = propagate(p, pts);
            if(!delta.isEmpty() ) {
                if(p instanceof CSVar csX) {
                    Var x = csX.getVar();
                    for(CSObj csObj : delta) {
                        if(taintAnalysis.isObjectTaint(csObj.getObject() ) ) {
                            continue; // skip normal points-to analysis for taint objects
                        }

                        for(LoadField ldf : x.getLoadFields() ) { // v = x.f
                            if(ldf.getFieldAccess() instanceof InstanceFieldAccess itfa) {
                                addPFGEdge(
                                        csManager.getInstanceField(csObj, itfa.getFieldRef().resolve() ),
                                        csManager.getCSVar(csX.getContext(), ldf.getLValue() )
                                );
                            }
                        }
                        for(StoreField stf : x.getStoreFields() ) { // x.f = v
                            if(stf.getFieldAccess() instanceof InstanceFieldAccess itfa) {
                                addPFGEdge(
                                        csManager.getCSVar(csX.getContext(), stf.getRValue() ),
                                        csManager.getInstanceField(csObj, itfa.getFieldRef().resolve() )
                                );
                            }
                        }
                        for(LoadArray lda : x.getLoadArrays() ) { // v = x[i]
                            addPFGEdge(
                                    csManager.getArrayIndex(csObj),
                                    csManager.getCSVar(csX.getContext(), lda.getLValue() )
                            );
                        }
                        for(StoreArray sta : x.getStoreArrays() ) { // x[i] = v
                            addPFGEdge(
                                    csManager.getCSVar(csX.getContext(), sta.getRValue() ),
                                    csManager.getArrayIndex(csObj)
                            );
                        }
                        processCall(csX, csObj);
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
        //  finish me
        // return null;
        PointsToSet delta = PointsToSetFactory.make();
        for(CSObj csObj : pointsToSet) {
            if(!pointer.getPointsToSet().contains(csObj) ) {
                delta.addObject(csObj);
            }
        }
        if(!delta.isEmpty() ) {
            pointer.getPointsToSet().addAll(delta);
            for(Pointer np : pointerFlowGraph.getSuccsOf(pointer) ) {
                workList.addEntry(np, delta);
            }

            // propagate taint objects across taint flow edges...
            PointsToSet taintObjects = PointsToSetFactory.make();
            for(CSObj csObj : delta) {
                if(taintAnalysis.isObjectTaint(csObj.getObject() ) ) {
                    taintObjects.addObject(csObj);
                }
            }
            if(!taintObjects.isEmpty() ) {
                for(Pair<Pointer, Type> npt : taintAnalysis.getTaintFlowGraph().getTaintSuccessors(pointer) ) {
                    for(CSObj taintObject : taintObjects) {
                        workList.addEntry(npt.first(), PointsToSetFactory.make(
                                taintAnalysis.getTaintObjectWithNewType(taintObject, npt.second() ) ) );
                    }
                }
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // finish me
        for(Invoke invoke : recv.getVar().getInvokes() ) {
            JMethod callee = resolveCallee(recvObj, invoke);

            //if(callee == null) {continue; }
            // This is a workaround, but it hides the truth for why the call site cannot be resolved.

            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
            CallKind callKind = getCallKind(invoke);

            workList.addEntry(
                    csManager.getCSVar(calleeContext, callee.getIR().getThis() ),
                    PointsToSetFactory.make(recvObj)
            );
            if(callGraph.addEdge(new Edge<>(callKind, csCallSite, csCallee) ) ) {
                addReachable(csCallee);
                int paramCount = callee.getParamCount();
                for(int i = 0; i < paramCount; ++i) {
                    addPFGEdge(
                            csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(i) ),
                            csManager.getCSVar(csCallee.getContext(), callee.getIR().getParam(i) )
                    );
                }
                if(invoke.getResult() != null) {
                    for(Var retVar : callee.getIR().getReturnVars() ) {
                        addPFGEdge(
                                csManager.getCSVar(csCallee.getContext(), retVar),
                                csManager.getCSVar(recv.getContext(), invoke.getResult() )
                        );
                    }

                    // if this callee is a source
                    CSObj csTaintObject = taintAnalysis.makeTaintObject(invoke, callee,
                            csManager.getCSMethod(recv.getContext(), invoke.getContainer() ) );
                    if(csTaintObject != null) {
                        workList.addEntry(
                                csManager.getCSVar(recv.getContext(), invoke.getResult() ),
                                PointsToSetFactory.make(csTaintObject)
                        );
                    }
                }

                // manipulate taint transfers
                Set<Pair<Pointer, Pair<Pointer, Type> > > edges = taintAnalysis.analyseTaintFlowEdges(csCallSite, csCallee);
                addTaintFGEdges(edges);

                // record taint sink sites
                Set<Integer> indexes = taintAnalysis.getTaintSinkIndex(callee);
                if(!indexes.isEmpty() ) {
                    for(Integer index : indexes) {
                        taintAnalysis.addTaintSinkSite(csCallSite, index);
                    }
                }
            }
        }
    }

    private CallKind getCallKind(Invoke invoke) {
        if(invoke.isStatic() ) {
            return CallKind.STATIC;
        }
        else if(invoke.isDynamic() ) {
            return CallKind.DYNAMIC;
        }
        else if(invoke.isInterface() ) {
            return CallKind.INTERFACE;
        }
        else if(invoke.isSpecial() ) {
            return CallKind.SPECIAL;
        }
        else if(invoke.isVirtual() ) {
            return CallKind.VIRTUAL;
        }
        else {
            throw new AnalysisException("No such callkind");
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

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
