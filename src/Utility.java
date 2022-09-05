import org.jetbrains.annotations.Nullable;
import soot.*;
import soot.jimple.*;
import soot.toolkits.scalar.Pair;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Utility {

    // One abstract class may be implemented by multiple classes.
    public static Map<SootClass, Set<SootClass>> abstractClassToImplementedClasses = new HashMap<SootClass, Set<SootClass>>();
    public Utility() {
    }

    public static List<SootMethod> getMethodsOfClass(String className) {
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        if (cls == null) { // the given class is not exist
            return null;
        }
        return cls.getMethods();
    }

    public static InvokeExpr getInvokeOfUnit(Unit unit) {
        if(unit == null) return null;
        if (unit instanceof AssignStmt){
            AssignStmt as = (AssignStmt) unit;
            return getInvokeOfAssignStmt(as);
        } else if(unit instanceof InvokeStmt){
            return ((InvokeStmt) unit).getInvokeExpr();
        }
        return null;
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

    public static Value getParameter(SootMethod method, Integer parameter_index) {
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


    public static boolean isUsedValueOfAssignment(AssignStmt as, Value v) {
        if(as == null || v == null) return false;
        List<ValueBox> vbs = as.getUseBoxes();
        for (ValueBox vb : vbs) {
            if (vb.getValue().equals(v)) return true;
        }
        return false;
    }

    public static boolean isDefValueOfAssignment(AssignStmt as, Value v){
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

    public static List<String> stringsToList(String[] strings){
        if (strings == null) return null;
        List<String> list = new ArrayList<>();
        for(String s : strings){
            list.add(s);
        }
        return list;
    }
    public static List<String> intToList(int i){
        if (i < 0) return null;
        List<String> list = new ArrayList<>();
        for(int j =0; j<i;j++){
            list.add(((Integer) j).toString());
        }
        return list;
    }

    public static boolean areRelatedNames(String element_name, String method_name){
        if(element_name.contains("-")){
            element_name = element_name.replace("-","");
        }
        method_name = method_name.toLowerCase();
        return method_name.contains(element_name);
    }

    public static boolean isNumeric(String s){
        Pattern pattern = Pattern.compile("[0-9]*");
        Matcher isNum = pattern.matcher(s);
        if(isNum.matches()) return true;
        return false;
    }

    public static void printSymbols(String symbol){
        String s = "";
        for(int i = 0; i<100;i++){
            s+=symbol;
        }
        System.out.println(s);
    }

    public static void initializeAbstractClassesInfo(){
        for(SootClass cls : Scene.v().getClasses()){
            if(cls.isConcrete()) { // Implemented class.
                for (SootClass abstract_cls : cls.getInterfaces()) {
                    Set<SootClass> implemented_classes = abstractClassToImplementedClasses.get(abstract_cls);
                    if (implemented_classes == null) {
                        implemented_classes = new HashSet<>();
                        implemented_classes.add(cls);
                        abstractClassToImplementedClasses.put(abstract_cls, implemented_classes);
                    } else {
                        implemented_classes.add(cls);
                    }
                }
            }
        }
    }
    public static Body getBodyOfAbstractMethod(InterfaceInvokeExpr ifi){
        SootMethod abstract_method = ifi.getMethod();
        SootClass abstract_cls = abstract_method.getDeclaringClass();
        Set<SootClass> implemented_classes = abstractClassToImplementedClasses.get(abstract_cls);
        if(implemented_classes == null){
            Utility.printSymbols("!");
            System.out.println("Special abstract class. Cannot find the implemented class of " + abstract_cls.getName());
            Utility.printSymbols("!");
            return null;
        }
        for(SootClass implemented_cls : implemented_classes){
            for(SootMethod method : implemented_cls.getMethods()){
                if(method.isConcrete()){
                    if(method.getSubSignature().equals(abstract_method.getSubSignature())){
                        System.out.println("abstract: " + abstract_method.getSubSignature());
                        if(method.getDeclaration().contains(" volatile ")) { // The return types of the abstract method and its implemented methods are different.
                            Body body = method.retrieveActiveBody();
                            for (Unit unit : body.getUnits()) {
                                InvokeExpr i = Utility.getInvokeOfUnit(unit);
                                if (i instanceof VirtualInvokeExpr && i.getMethod().getName().equals(abstract_method.getName())) {
                                    System.out.println("implemented: " + i.getMethod().getSubSignature());
                                    return i.getMethod().retrieveActiveBody();
                                }
                            }
                        }
                        System.out.println("implemented: " + method.getSubSignature());
                        return method.retrieveActiveBody();
                    }
                }
            }
        }
        Utility.printSymbols("!");
        System.out.println("Special abstract method. Cannot find the implemented method of " + abstract_method.getSignature());
        Utility.printSymbols("!");
        return null;
    }

}


