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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import polyglot.ast.Call;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // - finish me

        Queue<JMethod> methods = new LinkedList<>();
        methods.add(entry);
        while(!methods.isEmpty() ) {
            JMethod m = methods.remove();
            if(callGraph.reachableMethods.contains(m) ) {
                continue;
            }
            callGraph.addReachableMethod(m);
            callGraph.callSitesIn(m).forEach((cs) -> {
                CallKind callKind = CallGraphs.getCallKind(cs);
                Set<JMethod> targetMethods = resolve(cs);
                for(JMethod t : targetMethods) {
                    if(!methods.contains(t) ) {
                        methods.add(t);
                    }
                    Edge<Invoke, JMethod> e = new Edge<>(callKind, cs, t);
                    callGraph.addEdge(e);
                }
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        //  - finish me
        //return null;
        Set<JMethod> targetMethods = new HashSet<>();

        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        JClass declaredClass = callSite.getMethodRef().getDeclaringClass();

        CallKind callKind = CallGraphs.getCallKind(callSite);
        if(callKind == CallKind.STATIC || callKind == CallKind.SPECIAL) {
            targetMethods.add(dispatch(declaredClass, subsignature) );
        }
        else if(callKind == CallKind.VIRTUAL) {
            for(JClass c : getAllSubclasses(declaredClass)) {
                targetMethods.add(dispatch(c, subsignature) );
            }
        }
        else if(callKind == CallKind.INTERFACE) {
            Set<JClass> allSubInterfaces = getAllSubInterfaces(declaredClass); // interfaces can be inherited
            Set<JClass> allImplementations = new HashSet<>();
            for(JClass subInterface : allSubInterfaces) {
                allImplementations.addAll(hierarchy.getDirectImplementorsOf(subInterface) );
            }
            Set<JClass> allSubclasses = new HashSet<>();
            for(JClass c : allImplementations) {
                allSubclasses.addAll(getAllSubclasses(c) );
            }
            for(JClass c : allSubclasses) {
                targetMethods.add(dispatch(c, subsignature) );
            }
        }
        else {
            // do nothing
        }

        return targetMethods;
    }

    private Set<JClass> getAllSubInterfaces(JClass topInterface) {
        Set<JClass> result = new HashSet<>();
        result.add(topInterface);
        for(JClass subInterface : hierarchy.getDirectSubinterfacesOf(topInterface) ) {
            result.addAll(getAllSubInterfaces(subInterface) );
        }
        return result;
    }
    private Set<JClass> getAllSubclasses(JClass topClass) {
        Set<JClass> result = new HashSet<>();
        if(!topClass.isAbstract() ) { // abstract classes have no bodies
            result.add(topClass);
        }
        for(JClass subclass : hierarchy.getDirectSubclassesOf(topClass) ) {
            result.addAll(getAllSubclasses(subclass) );
        }
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        //  - finish me
        JMethod methodDecleared = jclass.getDeclaredMethod(subsignature);
        if(methodDecleared != null) {
            return methodDecleared;
        }
        else {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        // return null;
    }
}
