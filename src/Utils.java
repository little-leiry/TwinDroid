import soot.*;
import soot.jimple.*;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Utils {

    // One abstract class may be implemented by multiple classes.
    public static Map<SootClass, Set<SootClass>> abstractClassToImplementedClasses = new HashMap<SootClass, Set<SootClass>>();
    public Utils() {
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

    // Judge whether a value:
    // 1) is one of the assignment's use values and
    // 2) this value does not appear in the left of the assignment.
    public static boolean isRightValueOfAssignStmt(AssignStmt as, Value v) {
        if(as == null || v == null) return false;
        List<ValueBox> vbs = as.getUseBoxes();
        Value left_value = as.getLeftOp();
        for (ValueBox vb : vbs) {
            Value use_value = vb.getValue();
            if (use_value.equals(v) && !left_value.toString().contains(v.toString())) return true;
        }
        return false;
    }

    public static boolean hasRightValueOfAssignStmt(AssignStmt as, List<Value> values) {
        if(as == null || values == null) return false;
        for(Value v : values){
            if(isRightValueOfAssignStmt(as, v)) return true;
        }
        return false;
    }

    public static boolean isLeftValueOfAssignStmt(AssignStmt as, Value v){
        if(as==null || v == null) return false;
        if(as.getLeftOp().equals(v)) return true;
        return false;
    }

    public static int hasLeftValueOfAssignStmt(AssignStmt as, List<Value> values){
        if(as==null || values==null) return -1;
        for(Value v : values){
            if(isLeftValueOfAssignStmt(as, v)) return values.indexOf(v);
        }
        return -1;
    }

    public static int isParameterOfInvokeStmt(InvokeExpr i, Value v) {
        if(i == null || v == null) return -1;
        List<Value> parameters = i.getArgs();
        if (parameters.contains(v)) {
            return parameters.indexOf(v);
        }
        return -1;
    }

    public static int hasParameterOfInvokeStmt(InvokeExpr i, List<Value> values) {
        if(i == null || values == null) return -1;
        for(Value v : values){
            int index = isParameterOfInvokeStmt(i, v);
            if(index != -1) return index;
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

    public static void printPartingLine(String symbol, PrintWriter pw){
        String s = "";
        for(int i = 0; i<100;i++){
            s+=symbol;
        }
        pw.println(s);
    }

    public static void printPartingLine(String symbol){
        String s = "";
        for(int i = 0; i<100;i++){
            s+=symbol;
        }
        System.out.println(s);
    }


    public static String generatePartingLine(String symbol){
        String s = "";
        for(int i = 0; i<100;i++){
            s+=symbol;
        }
        return s;
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
    public static SootMethod getImplementedMethodOfAbstractMethod(InterfaceInvokeExpr ifi){
        Value base = ifi.getBase();
        SootMethod abstract_method = ifi.getMethod();
        SootClass abstract_cls = null;
        // Get the abstract class.
        if(base!=null) {
            abstract_cls = ((RefType) base.getType()).getSootClass();
        } else {
            abstract_cls = abstract_method.getDeclaringClass();
        }
        //System.out.println(ifi);
        //System.out.println("--- abstract class: " + abstract_cls);
        Log.logData(Tainted.analysis_data, "+ " + ifi);
        Log.logData(Tainted.analysis_data, "--- abstract class: " + abstract_cls);
        // Get the corresponding implemented classes.
        Set<SootClass> implemented_classes = abstractClassToImplementedClasses.get(abstract_cls);
        if(implemented_classes == null){
            Utils.printPartingLine("!");
            System.out.println("Special abstract class. Cannot find the implemented class of " + abstract_cls.getName());
            Utils.printPartingLine("!");
            return null;
        }
        if(implemented_classes.size()>1){
            Utils.printPartingLine("!");
            System.out.println("Special abstract classes, more than one implemented classes: " + implemented_classes);
            Utils.printPartingLine("!");
        }
        //Choose the first found implemented method.
        for(SootClass implemented_cls : implemented_classes){
            for(SootMethod method : implemented_cls.getMethods()){
                if(method.isConcrete()){
                    if(method.getSubSignature().equals(abstract_method.getSubSignature())){
                        //System.out.println("--- abstract method: " + abstract_method.getSignature());
                        Log.logData(Tainted.analysis_data, "--- abstract method: " + abstract_method.getSignature());
                        if(method.getDeclaration().contains(" volatile ")) { // The return types of the abstract method and its implemented method are different.
                            Body body = method.retrieveActiveBody();
                            for (Unit unit : body.getUnits()) {
                                InvokeExpr i = Utils.getInvokeOfUnit(unit);
                                if (i instanceof VirtualInvokeExpr){
                                    SootMethod implemented_method = i.getMethod();
                                    if(implemented_method.getName().equals(abstract_method.getName()) &&
                                            implemented_method.getParameterTypes().equals(abstract_method.getParameterTypes())) { // The actually implemented method.
                                        //System.out.println("--- implemented method: " + implemented_method.getSignature());
                                        Log.logData(Tainted.analysis_data, "--- implemented method: " + implemented_method.getSignature());
                                        return implemented_method;
                                    }
                                }
                            }
                        }
                        //System.out.println("--- implemented method: " + method.getSignature());
                        Log.logData(Tainted.analysis_data, "--- implemented method: " + method.getSignature());
                        return method;
                    }
                }
            }
        }
        Utils.printPartingLine("!");
        System.out.println("Special abstract method. Cannot find the implemented method of " + abstract_method.getSignature());
        Utils.printPartingLine("!");
        return null;
    }

    public static List<Unit> bodyToList(Body body){
        List<Unit> b = new ArrayList<>();
        if(body==null) return b;
        for(Unit unit : body.getUnits()){
            b.add(unit);
        }
        return b;
    }

    public static int getIndexOfUnit(Body body, Unit unit){
        if(body==null || unit == null) return -1;
        return bodyToList(body).indexOf(unit);
    }

    public static String getConcreteAssignmentOfByteValue(Body body, Unit unit, Value v){
        Unit pre = body.getUnits().getPredOf(unit);
        if(pre instanceof AssignStmt){
            AssignStmt as = (AssignStmt) pre;
            if(as.getDefBoxes().get(0).getValue().equals(v)){
                if(as.getUseBoxes().size() == 1){
                    Value vv = as.getUseBoxes().get(0).getValue();
                    if(vv.getType().toString().equals("int")){
                        return vv.toString();
                    }
                }
            }
        }
        return null;
    }

    public static <T> List<T> deepCopy(List<T> src) {
        List<T> dest = new ArrayList<>();
        if(src == null){
            return dest;
        }
        for(T object : src){
            dest.add(object);
        }
        return dest;
    }

    public static boolean isExpress(String str){
        char[] ops = {'&', '|', '!','+', '-', '*', '/', '%', '^'};
        for(char op : ops){
            if(str.contains(String.valueOf(op))) return true;
        }
        return false;
    }

    public static void pause(){
        try{
            System.out.println("Enter anything to continue ...");
            char in = (char) System.in.read();
        } catch (IOException e){
            e.printStackTrace();
        }
    }

    public static boolean hasDuplicatedItems(List<List<Integer>> paths){
        long count = paths.stream().distinct().count();
        if(count == paths.size()){
            return false;
        }else{
            return true;
        }
    }
}


