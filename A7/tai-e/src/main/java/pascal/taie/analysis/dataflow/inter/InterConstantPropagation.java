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

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Multimap<Var, Var> aliasMap = HashMultimap.create();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

        // calculate alias information by the brute force method
        Object[] vars = pta.getVars().toArray();
        for(Object o : vars) {
            Var v = (Var)o;
            aliasMap.put(v, v);
        }
        int varsCount = vars.length;
        for(Obj obj : pta.getObjects() ) {
            for(int i = 0; i < varsCount; ++i) {
                for(int j = i + 1; j < varsCount; ++j) {
                    Var va = (Var)vars[i];
                    Var vb = (Var)vars[j];
                    if(aliasMap.get(va).contains(vb) ) {
                        continue;
                    }
                    if(pta.getPointsToSet(va).contains(obj)
                            && pta.getPointsToSet(vb).contains(obj) ) {
                        aliasMap.get(va).add(vb);
                        aliasMap.get(vb).add(va);
                    }
                }
            }
        }

    }
    public Collection<Var> FetchAliasVarSetForVar(Var v) {
        return aliasMap.get(v);
    }


    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        //  finish me
        //return false;
        if(stmt instanceof DefinitionStmt d
                && d.getLValue() instanceof Var v
                && ConstantPropagation.canHoldInt(v) ) {
            if(d instanceof LoadField dlf) {
                return transferLoadFieldNode(dlf, in, out);
            }
            else if(d instanceof LoadArray dla) {
                return transferLoadArrayNode(dla, in, out);
            }
        }
        return cp.transferNode(stmt, in, out);  // other cases
    }

    private boolean transferLoadFieldNode(LoadField stmt, CPFact in, CPFact out) {
        CPFact newOut = in.copy();
        Var def = stmt.getLValue();
        JField fieldLoad = stmt.getFieldRef().resolve();
        Value meetResult = Value.getUndef();
        if( stmt.isStatic() ) {
            for(Stmt s : icfg.getNodes() ) {
                if(s instanceof StoreField stf
                        && stf.getFieldRef().resolve().equals(fieldLoad) ) {
                    CPFact thereIn = solver.FetchConstantPropagationFactsInExternalProcedure(stf);
                    meetResult = cp.meetValue(meetResult, thereIn.get(stf.getRValue() ) );
                }
                if(meetResult.isNAC() ) {
                    break;
                }
            }
        }
        else {
            Var loadBase = ((InstanceFieldAccess)stmt.getFieldAccess() ).getBase();
            Collection<?> aliasSet = aliasMap.get(loadBase);
            for(Stmt s : icfg.getNodes() ) {
                if(s instanceof StoreField stf
                        && stf.getFieldAccess() instanceof InstanceFieldAccess ifa
                        && aliasSet.contains(ifa.getBase() )
                        && ifa.getFieldRef().resolve().equals(fieldLoad) ) {
                    CPFact thereIn = solver.FetchConstantPropagationFactsInExternalProcedure(stf);
                    meetResult = cp.meetValue(meetResult, thereIn.get(stf.getRValue() ) );
                }
                if(meetResult.isNAC() ) {
                    break;
                }
            }
        }
        newOut.update(def, meetResult);
        return out.copyFrom(newOut);
    }

    private boolean transferLoadArrayNode(LoadArray stmt, CPFact in, CPFact out) {
        CPFact newOut = in.copy();
        Var def = stmt.getLValue();
        // Value defValue = in.get(def); This is NOT necessary as the constant propagation is FLOW-SENSITIVE
        Collection<?> aliasSet = aliasMap.get(stmt.getArrayAccess().getBase() );
        Value indexValue = in.get(stmt.getArrayAccess().getIndex() );

        Value meetResult = Value.getUndef();
        for(Stmt s : icfg.getNodes() ) {
            if(s instanceof StoreArray sta
                    && aliasSet.contains(sta.getArrayAccess().getBase() ) ) {
                CPFact thereIn = solver.FetchConstantPropagationFactsInExternalProcedure(sta);
                Value storeIndexValue = thereIn.get(sta.getArrayAccess().getIndex() );
                if(indexValue.isUndef() || storeIndexValue.isUndef() ) {
                    continue; // not alias
                }
                else if(indexValue.isNAC() || storeIndexValue.isNAC() ) {
                    meetResult = cp.meetValue(meetResult, thereIn.get(sta.getRValue() ) );
                }
                else if(indexValue.getConstant() == storeIndexValue.getConstant() ) {
                    meetResult = cp.meetValue(meetResult, thereIn.get(sta.getRValue() ) );
                }

                if(meetResult.isNAC() ) {
                    break;
                }
            }
        }

        //defValue = cp.meetValue(defValue, meetResult);
        //newOut.update(def, defValue);
        newOut.update(def, meetResult);
        return out.copyFrom(newOut);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // - finish me
        //return null;
        CPFact fact = out.copy();
        return fact;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // - finish me
        //return null;
        CPFact fact = out.copy();
        if(edge.getSource().getDef().isPresent()
                && edge.getSource().getDef().get() instanceof Var v) {
            fact.remove(v);
        }
        return fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // finish me
        //return null;
        Invoke callSite = (Invoke) edge.getSource();
        int paramNum = edge.getCallee().getParamCount();
        CPFact fact = new CPFact();
        for(int i = 0; i < paramNum; ++i) {
            fact.update(
                    edge.getCallee().getIR().getParam(i),
                    callSiteOut.get(callSite.getInvokeExp().getArg(i)) );
        }
        return fact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // - finish me
        //return null;
        CPFact fact = new CPFact();

        if(edge.getCallSite().getDef().isPresent()
                && edge.getCallSite().getDef().get() instanceof Var def) {
            Value factVal = Value.getUndef();
            for(Var v : edge.getReturnVars()) {
                factVal = cp.meetValue(factVal, returnOut.get(v) );
            }
            fact.update(def, factVal);
        }

        return fact;
    }
}