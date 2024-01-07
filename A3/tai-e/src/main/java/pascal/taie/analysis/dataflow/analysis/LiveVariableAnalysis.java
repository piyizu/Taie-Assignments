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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import java.util.List;
import java.util.NoSuchElementException;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODOO - finish me
        // return null;
        SetFact<Var> exitSetFact = new SetFact<Var>();
        return exitSetFact;
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODOO - finish me
        // return null;
        SetFact<Var> initSetFact = new SetFact<Var>();
        return initSetFact;
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODOO - finish me

        if(fact == null) {
            return;
        }
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODOO - finish me
        // return false;

        if(out == null || in == null) return false;

        SetFact<Var> newIn = out.copy();

        try {
            LValue def = stmt.getDef().get();
            if(def instanceof Var)
                newIn.remove( (Var)def );
        } catch(NoSuchElementException e) {

        }

        getRValueVars(stmt.getUses(), newIn);

        if(in.equals(newIn))
            return false;
        in.set(newIn);
        return true;
    }

    private void getRValueVars(List<RValue> uses, SetFact<Var> set) {
        if(uses == null || uses.isEmpty()) return;
        for(RValue use : uses) {
            if(use instanceof Var) {
                set.add((Var) use);
            }
            else {
                getRValueVars(use.getUses(), set);
            }
        }
    }
}
