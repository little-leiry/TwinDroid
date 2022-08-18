import org.jetbrains.annotations.Nullable;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;

import java.util.ArrayList;
import java.util.List;

public class Utility {

    public Utility(){}

    public static List<SootMethod> getMethodsOfClass(String className){
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        if (cls == null){ // the given class is not exist
            return null;
        }
        return cls.getMethods();
    }

    public static InvokeExpr getCallee(Unit unit){
        if(unit instanceof InvokeStmt){
            InvokeStmt is =(InvokeStmt) unit;
            InvokeExpr invoke = is.getInvokeExpr();
            //System.out.println("---"+is);
            return invoke;
        }
        if(unit instanceof AssignStmt) {
            AssignStmt as = (AssignStmt) unit;
            if (as.containsInvokeExpr()) {
                InvokeExpr invoke = as.getInvokeExpr();
                return invoke;
            }
        }
        return null;
    }
    public static String getNameOfCallee(InvokeExpr callee){
        return callee.getMethod().getName();
    }

    public static String getSignatureOfCallee(InvokeExpr callee){
        return callee.getMethod().getSignature();
    }


    public static Boolean containValue(AssignStmt as, Value v){
        for(ValueBox vb : as.getUseBoxes()){
            if(vb.getValue().equals(v)) return true;
        }
        return false;
    }

    public static Boolean isParameter(InvokeExpr i, Value v){
        return i.getArgs().contains(v);
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

    public static Body getBodyOfMethod(String signature){
        SootMethod sm = Scene.v().getMethod(signature);
        if(sm.isConcrete()){
            return sm.retrieveActiveBody();
        }
        return null;
    }
}
