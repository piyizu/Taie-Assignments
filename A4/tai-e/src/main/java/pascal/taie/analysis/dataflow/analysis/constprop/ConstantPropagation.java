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

package pascal.taie.analysis.dataflow.analysis.constprop;

import org.checkerframework.checker.signature.qual.BinaryNameWithoutPackage;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import soot.jimple.NewArrayExpr;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.concurrent.ExecutionException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // done - finish me
        // return new CPFact();
        CPFact fact = new CPFact();

        for(Var v : cfg.getIR().getParams() ) {
            if(canHoldInt(v) ) {
                fact.update(v, Value.getNAC());
            }
            else {
                fact.update(v, Value.getUndef());
            }
        }

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // done - finish me
        // return null;
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // done - finish me
        fact.forEach((v, val) -> {
            target.update(v, meetValue(val, target.get(v)));
        } );
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // done - finish me
        // return null;
        if(v1.equals(v2)) {
            return v1;
        }
        else if ( v1.isNAC() || v2.isNAC() ){
            return Value.getNAC();
        }
        else if ( v1.isConstant() && v2.isConstant() ){
            return Value.getNAC();
        }
        else if( v1.isConstant() ) {
            return v1;
        }
        else if( v2.isConstant() ) {
            return v2;
        }
        else {
            throw new AnalysisException("Impossible Meet");
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // done - finish me
        // return false;
        if(in == null || out == null) return false;

        if(stmt instanceof DefinitionStmt
        && ((DefinitionStmt<LValue, RValue>) stmt).getLValue() instanceof Var v
        && canHoldInt(v) ) {
            CPFact newOut = in.copy();
            newOut.update(v, evaluate( ((DefinitionStmt<LValue, RValue>) stmt).getRValue(), in) );
            return out.copyFrom(newOut);
        }

        return out.copyFrom(in); // DO NOT RETURN FALSE HERE, OR YOU WOULD BLOCK THE PROPAGATION!
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    public static boolean isInIntTypeFamily(Type type) {
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // done - finish me
        // return null;

        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof Var v) {
            if(!canHoldInt(v) ) {
                return Value.getUndef();
            }
            return in.get(v);
        } else if (exp instanceof BinaryExp) {
            Var op1 = ((BinaryExp) exp).getOperand1();
            Var op2 = ((BinaryExp) exp).getOperand2();
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();

            // This may be unnecessary as cast operations would have been done earlier.
            if(!canHoldInt(op1) || !canHoldInt(op2) ) {
                return Value.getUndef();      // Ignore unrelated types
            }

            if(in.get(op1).isNAC() || in.get(op2).isNAC()) {
                return Value.getNAC();
            }
            else if(in.get(op1).isUndef() || in.get(op2).isUndef() ) {
                return Value.getUndef();
            }
            else {
                if(op == ArithmeticExp.Op.ADD) {
                    return Value.makeConstant(in.get(op1).getConstant() + in.get(op2).getConstant() );
                }
                else if(op == ArithmeticExp.Op.SUB) {
                    return Value.makeConstant(in.get(op1).getConstant() - in.get(op2).getConstant() );
                }
                else if(op == ArithmeticExp.Op.MUL) {
                    return Value.makeConstant(in.get(op1).getConstant() * in.get(op2).getConstant() );
                }
                else if(op == ArithmeticExp.Op.DIV) {
                    if(in.get(op2).getConstant() == 0) {
                        return Value.getUndef();
                    }
                    else {
                        return Value.makeConstant(in.get(op1).getConstant() / in.get(op2).getConstant() );
                    }
                }
                else if(op == ArithmeticExp.Op.REM) {
                    if(in.get(op2).getConstant() == 0) {
                        return Value.getUndef();
                    }
                    else {
                        return Value.makeConstant(in.get(op1).getConstant() % in.get(op2).getConstant() );
                    }
                }
                else if(op == BitwiseExp.Op.OR) {
                    return Value.makeConstant(in.get(op1).getConstant() | in.get(op2).getConstant() );
                }
                else if(op == BitwiseExp.Op.AND) {
                    return Value.makeConstant(in.get(op1).getConstant() & in.get(op2).getConstant() );
                }
                else if(op == BitwiseExp.Op.XOR) {
                    return Value.makeConstant(in.get(op1).getConstant() ^ in.get(op2).getConstant() );
                }
                else if(op == ConditionExp.Op.EQ) {
                    if(in.get(op1).getConstant() == in.get(op2).getConstant()) {
                        return Value.makeConstant(1);
                    }
                    else {
                        return Value.makeConstant(0);
                    }
                }
                else if(op == ConditionExp.Op.NE) {
                    if(in.get(op1).getConstant() != in.get(op2).getConstant()) {
                        return Value.makeConstant(1);
                    }
                    else {
                        return Value.makeConstant(0);
                    }
                }
                else if(op == ConditionExp.Op.LT) {
                    if(in.get(op1).getConstant() < in.get(op2).getConstant()) {
                        return Value.makeConstant(1);
                    }
                    else {
                        return Value.makeConstant(0);
                    }
                }
                else if(op == ConditionExp.Op.LE) {
                    if(in.get(op1).getConstant() <= in.get(op2).getConstant()) {
                        return Value.makeConstant(1);
                    }
                    else {
                        return Value.makeConstant(0);
                    }
                }
                else if(op == ConditionExp.Op.GE) {
                    if(in.get(op1).getConstant() >= in.get(op2).getConstant()) {
                        return Value.makeConstant(1);
                    }
                    else {
                        return Value.makeConstant(0);
                    }
                }
                else if(op == ConditionExp.Op.GT) {
                    if(in.get(op1).getConstant() > in.get(op2).getConstant()) {
                        return Value.makeConstant(1);
                    }
                    else {
                        return Value.makeConstant(0);
                    }
                }
                else if(op == ShiftExp.Op.SHL) {
                    return Value.makeConstant(in.get(op1).getConstant() << in.get(op2).getConstant() );
                }
                else if(op == ShiftExp.Op.SHR) {
                    return Value.makeConstant(in.get(op1).getConstant() >> in.get(op2).getConstant() );
                }
                else if(op == ShiftExp.Op.USHR) {
                    return Value.makeConstant(in.get(op1).getConstant() >>> in.get(op2).getConstant() );
                }
                else {
                    throw new AnalysisException("Unrecognised Operator");
                }
            }
        } else if (exp instanceof NegExp) {
            Var v = ((NegExp) exp).getValue();
            if(!canHoldInt(v) ) {
                return Value.getUndef();
            }
            Value originVal = in.get(v);
            if(originVal.isConstant() ) {
                return Value.makeConstant(-originVal.getConstant() );
            }
            else {
                return originVal;
            }
        } else if(exp instanceof FieldAccess fieldAccess) {
            Type type = fieldAccess.getType();
            if(isInIntTypeFamily(type) ) {
                return Value.getNAC();
            }
            else {
                return Value.getUndef();
            }
        } else if(exp instanceof ArrayAccess arrayAccess) {
            Type type = arrayAccess.getType();
            if(isInIntTypeFamily(type) ) {
                return Value.getNAC();
            }
            else {
                return Value.getUndef();
            }
        } else if(exp instanceof NewExp newExp) {
            return Value.getUndef();
        } else {
            return Value.getNAC();
        }
    }
}
