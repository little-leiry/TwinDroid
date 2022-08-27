import org.jetbrains.annotations.Nullable;
import soot.*;
import soot.jimple.*;

import java.util.ArrayList;
import java.util.List;

public class Utility {

    public Utility() {
    }

    public static List<SootMethod> getMethodsOfClass(String className) {
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        if (cls == null) { // the given class is not exist
            return null;
        }
        return cls.getMethods();
    }

    public static InvokeExpr getCallee(InvokeStmt is) {
        InvokeExpr invoke = is.getInvokeExpr();
        return invoke;
    }

    public static InvokeExpr getInvokeOfAssignStmt(AssignStmt as) {
        if(as==null) return null;
        if (as.containsInvokeExpr()) {
            InvokeExpr invoke = as.getInvokeExpr();
            return invoke;
        }
        return null;
    }

    public static Value getBaseOfInvokeExpr(InvokeExpr i){
        if (i instanceof VirtualInvokeExpr) {
            return ((VirtualInvokeExpr) i).getBase();
        } else if (i instanceof InterfaceInvokeExpr) {
            return ((InterfaceInvokeExpr) i).getBase();
        } else if (i instanceof SpecialInvokeExpr) {
            return ((SpecialInvokeExpr) i).getBase();
        }
        return null;
    }

    public static String getNameOfCallee(InvokeExpr callee) {
        return callee.getMethod().getName();
    }

    public static String getSignatureOfCallee(InvokeExpr callee) {
        return callee.getMethod().getSignature();
    }

    public static List<Body> getBodyOfMethod(String className, String methodName) {
        List<Body> bodies = new ArrayList<>();
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        for (SootMethod sm : cls.getMethods()) {
            if (sm.getName().equals(methodName)) {
                bodies.add(sm.retrieveActiveBody());
            }
        }
        return bodies;
    }

    public static Body getBodyOfMethod(String signature) {
        SootMethod sm = Scene.v().getMethod(signature);
        if (sm.isConcrete()) {
            return sm.retrieveActiveBody();
        }
        return null;
    }

    public static Value transfer(SootMethod method, Integer parameter_index) {
        if(method == null) return null;
        Value parameter = null;
        if(method.isConcrete()){
            Body body = method.retrieveActiveBody();
            for(Unit unit:body.getUnits()){
                if(unit instanceof IdentityStmt){
                    IdentityStmt is = (IdentityStmt) unit;
                    if(is.getRightOp().toString().contains("@parameter" + parameter_index.toString())){
                        parameter = is.getLeftOp();
                        return parameter;
                    }
                }
            }
        }
        return parameter;
    }


    public static Boolean isUsedValueOfAssignment(AssignStmt as, Value v) {
        if(as == null || v == null) return false;
        List<ValueBox> vbs = as.getUseBoxes();
        for (ValueBox vb : vbs) {
            if (vb.getValue().equals(v)) return true;
        }
        return false;
    }

    public static Boolean isDefValueOfAssignment(AssignStmt as, Value v){
        if(as==null || v == null) return false;
        for(ValueBox vb: as.getDefBoxes()){
            if (vb.getValue().equals(v)) return true;
        }
        return false;
    }

    public static int isParameter(InvokeExpr i, Value v) {
        if(i == null || v == null) return -1;
        List<Value> parameters = i.getArgs();
        if (parameters.contains(v)) {
            return parameters.indexOf(v);
        }
        return -1;
    }
}


