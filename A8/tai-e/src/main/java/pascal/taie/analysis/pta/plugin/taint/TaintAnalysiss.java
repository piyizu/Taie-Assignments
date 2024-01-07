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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    //  finish me

    public class TaintFlowGraph { // assists taint flow transfer analysis
        private final MultiMap<Pointer, Pair<Pointer, Type> > edges = Maps.newMultiMap();

        public boolean addTaintFGEdge(Pointer source, Pointer target, Type targetType) {
            // returns true if the TFG is changed
            return edges.put(source, new Pair<>(target, targetType) );
        }
        public Collection<Pair<Pointer, Type> > getTaintSuccessors(Pointer source) {
            return edges.get(source);
        }
    }
    private TaintFlowGraph taintFlowGraph = new TaintFlowGraph();
    private Set<Pair<CSCallSite, Integer> > taintSinkSites = new HashSet<>();
    // <Source, SinkSite, TaintSinkIndex> --> <?, csCallsite, Integer>

    public void addTaintSinkSite(CSCallSite csCallSite, Integer index) {
        taintSinkSites.add(new Pair<>(csCallSite, index) );
    }

    public TaintFlowGraph getTaintFlowGraph() {
        return taintFlowGraph;
    }

    public boolean isObjectTaint(Obj obj) {
        return manager.isTaint(obj);
    }
    public CSObj makeTaintObject(Invoke invoke, JMethod callee, CSMethod methodContainingCallsite) {
        // makes a new taint object if the callee is a source of taint
        // returns the new taint it has made or null if the callee is not a source
        Type type = null;
        for(Source source : config.getSources() ) {
            if(source.method().equals(callee) ) {
                type = source.type();
                break;
            }
        }
        if(type != null) {
            Obj taintObj = manager.makeTaint(invoke, type);
            Context taintContext = getTaintContext(methodContainingCallsite, taintObj);
            return csManager.getCSObj(taintContext, taintObj);
        }
        return null;
    }

    public CSObj getTaintObjectWithNewType(CSObj csTaintObject, Type newType) {
        if(csTaintObject.getObject().getType() == newType) {
            return csTaintObject;
        }
        Obj newTaintObject = manager.makeTaint(
                manager.getSourceCall(csTaintObject.getObject() ), newType);
        return csManager.getCSObj(csTaintObject.getContext(), newTaintObject);
    }

    public Set<Pair<Pointer, Pair<Pointer, Type> > > analyseTaintFlowEdges(CSCallSite csCallSite, CSMethod csCallee) {
        Set<Pair<Pointer, Pair<Pointer, Type> > > edgesAnalysed = new HashSet<>();
        JMethod callee = csCallee.getMethod();
        for(TaintTransfer taintTransfer : config.getTransfers() ) {
            if(taintTransfer.method().equals(callee) ) {
                int from = taintTransfer.from();
                int to = taintTransfer.to();
                Type type = taintTransfer.type();
                CSVar csResult = csCallSite.getCallSite().getResult() == null ? null : csManager.getCSVar(
                        csCallSite.getContext(),
                        csCallSite.getCallSite().getResult()
                );
                CSVar csBase = csCallSite.getCallSite().isStatic() ? null : csManager.getCSVar(
                        csCallSite.getContext(),
                        ((InvokeInstanceExp)csCallSite.getCallSite().getInvokeExp()).getBase()
                );
                CSVar csArg = from < 0 ? null : csManager.getCSVar(
                        csCallSite.getContext(),
                        csCallSite.getCallSite().getInvokeExp().getArg(from)
                );
                if(from >= 0 && to == -1) {
                    // arg to base
                    if(csBase != null) {
                        edgesAnalysed.add(new Pair<>(csArg, new Pair<>(csBase, type) ) );
                    }
                }
                else if(from >= 0 && to == -2) {
                    // arg to result
                    if(csResult != null) {
                        edgesAnalysed.add(new Pair<>(csArg, new Pair<>(csResult, type) ) );
                    }
                }
                else if(from == -1 && to == -2) {
                    // base to result
                    if(csBase != null && csResult != null) {
                        edgesAnalysed.add(new Pair<>(csBase, new Pair<>(csResult, type) ) );
                    }
                }
            }
        }
        return edgesAnalysed;
    }

    public Context getTaintContext(CSMethod methodContainingCallsite, Obj taint) {
        // in this homework, we are only required to use empty-context taint objects
        return emptyContext;
        //return solver.getContextSelector().selectHeapContext(methodContainingCallsite, taint);
    }

    public Set<Integer> getTaintSinkIndex(JMethod method) {
        // returns taint sink indexes, empty if not a taint sink
        Set<Integer> indexes = new HashSet<>();
        for(Sink sink : config.getSinks() ) {
            if(sink.method().equals(method) ) {
                indexes.add(Integer.valueOf(sink.index() ) );
            }
        }
        return indexes;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        //  finish me
        // You could query pointer analysis results you need via variable result.

        for(Pair<?, ?> taintSinkSite : taintSinkSites) {
            int index = ((Integer) taintSinkSite.second() ).intValue();
            CSCallSite csCallSite = (CSCallSite) taintSinkSite.first();
            Set<CSObj> pts = result.getPointsToSet(
                    solver.getCSManager().getCSVar(
                            csCallSite.getContext(),
                            csCallSite.getCallSite().getInvokeExp().getArg(index)
                    )
            );
            for(CSObj csObj : pts) {
                if(manager.isTaint(csObj.getObject() ) ) {
                    taintFlows.add(new TaintFlow(
                            manager.getSourceCall(csObj.getObject() ),
                            csCallSite.getCallSite(),
                            index)
                    );
                }
            }
        }

        return taintFlows;
    }
}
