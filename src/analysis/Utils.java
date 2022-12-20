package analysis;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.Block;

import java.io.*;
import java.nio.channels.FileChannel;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Utils {

    // One abstract class may be implemented by multiple classes.
    public static Map<SootClass, Set<SootClass>> interfaceClassToImplementedClasses = new HashMap<SootClass, Set<SootClass>>();
    public static Map<SootClass, Set<SootClass>> interfaceClassToSubInterfaceClasses = new HashMap<SootClass, Set<SootClass>>();
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
        if(i==null) return null;

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
                try {
                    bodies.add(sm.retrieveActiveBody());
                }catch(Exception e){
                    e.printStackTrace();
                    System.out.println(sm.getSignature());
                }
            }
        }
        return bodies;
    }

    public static Body getBodyOfMethod(String signature) {
        SootMethod sm = Scene.v().getMethod(signature);
        if (sm.isConcrete()) {
            try {
                return sm.retrieveActiveBody();
            }catch (Exception e){
                System.out.println(signature);
                throw new RuntimeException(e);
            }
        }
        return null;
    }

    public static Value getParameterOfMethod(Body body, Integer parameter_index) {
        if(body == null) return null;

        for(Unit unit:body.getUnits()){
            if(unit instanceof IdentityStmt){
                IdentityStmt is = (IdentityStmt) unit;
                if(is.getRightOp().toString().contains("@parameter" + parameter_index.toString())){
                    return is.getLeftOp();
                }
            }
        }
        return null;
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

    public static Value getReturnValue(Body body){
        if(body == null) return null;

        for(Unit unit : body.getUnits()){
            if(unit instanceof ReturnStmt) {
                Value return_value = ((ReturnStmt) unit).getOp();
                if (!(return_value instanceof NullConstant)){
                    return ((ReturnStmt) unit).getOp();
                }
            }
        }
        return null;
    }

    // Judge whether a value:
    // 1) is one of the assignment's use values and
    // 2) this value appears in the right of the assignment.
    public static boolean isRightValueOfAssignStmt(AssignStmt as, Value v) {
        if(as == null || v == null) return false;

        // Data pre-processing.
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(ie!=null) {
            if (!v.getUseBoxes().isEmpty()) {
                v = v.getUseBoxes().get(0).getValue();
            }
        }

        List<ValueBox> vbs = as.getUseBoxes();
        for (ValueBox vb : vbs) {
            Value use_value = vb.getValue();
            if (use_value.equals(v) &&
                    as.getRightOp().toString().contains(v.toString())) {
                return true;
            }
        }
        return false;
    }

    public static List<Value> hasRightValuesOfAssignStmt(AssignStmt as, List<Value> values) {
        List<Value> result = new ArrayList<>();
        if(as == null || values == null) return result;
        for(Value v : values){
            if(isRightValueOfAssignStmt(as, v)){
                result.add(v);
            }
        }
        return result;
    }

    public static boolean isUseValueOfInvokeStmt(InvokeStmt is, Value v) {
        if(is == null || v == null) return false;
        if(!v.getUseBoxes().isEmpty()){
            v = v.getUseBoxes().get(0).getValue();
        }
        List<ValueBox> vbs = is.getUseBoxes();
        for (ValueBox vb : vbs) {
            Value use_value = vb.getValue();
            if (use_value.equals(v)) {
                return true;
            }
        }
        return false;
    }

    public static List<Value> hasUseValuesOfInvokeStmt(InvokeStmt is, List<Value> values) {
        List<Value> result = new ArrayList<>();
        if(is == null || values == null) return result;
        for(Value v : values){
            if(isUseValueOfInvokeStmt(is, v)){
                result.add(v);
            }
        }
        return result;
    }

    public static boolean isLeftValueOfAssignStmt(AssignStmt as, Value v){
        if(as==null || v == null) return false;

        // Data pre-processing.
        if(!v.getUseBoxes().isEmpty()){
            v = v.getUseBoxes().get(0).getValue();
        }

        if(as.getLeftOp().equals(v)) return true;
        return false;
    }

    public static Value hasLeftValueOfAssignStmt(AssignStmt as, List<Value> values){
        if(as==null || values==null) return null;
        for(Value v : values){
            if(isLeftValueOfAssignStmt(as, v)) {
                return v;
            }
        }
        return null;
    }

    public static int isParameterOfInvokeExpr(InvokeExpr i, Value v) {
        if(i == null || v == null) return -1;

        // Data pre-processing.
        if(!v.getUseBoxes().isEmpty()){
            v = v.getUseBoxes().get(0).getValue();
        }

        List<Value> parameters = i.getArgs();
        if (parameters.contains(v)) {
            return parameters.indexOf(v);
        }
        return -1;
    }

    public static List<Value> hasParametersOfInvokeExpr(InvokeExpr i, List<Value> values) {
        List<Value> result = new ArrayList<>();
        if(i == null || values == null) return result;
        for(Value v : values){
            if(isParameterOfInvokeExpr(i, v)!= -1) {
                result.add(v);
            }
        }
        return result;
    }

    public static boolean isCopyStmt(AssignStmt as){
        if(as == null) return false;
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(ie == null && as.getUseBoxes().size() == 1){
            String right_value_type = as.getRightOp().getType().toString();
            String left_value_type = as.getLeftOp().getType().toString();
            if(right_value_type.equals(left_value_type)){
                return true;
            }
        }
        return false;
    }

    // r7 = r4
    // r7 is a copy of r4
    public static boolean isCopyOfValue(AssignStmt as, Value value){
        if(as==null || value == null) return false;
        InvokeExpr ie = getInvokeOfAssignStmt(as);
        List<ValueBox> vbs = as.getUseBoxes();
        // There is a copy of value.
        if(vbs.size()==1 && ie == null){
            Value right_value = as.getRightOp();
            Value left_value = as.getLeftOp();
            if(value.equals(right_value) &&
                    value.getType().equals(left_value.getType())){
                return true;
            }
        }
        return false;
    }

    public static boolean hasCopyOfValues(AssignStmt as, List<Value> values){
        if(as==null || values == null) return false;
        for(Value v : values){
            if(isCopyOfValue(as, v) == true) return true;
        }
        return false;
    }

    public static boolean isMapValue(Value v){
        if(v==null) return false;
        String type = v.getType().toString();
        if(type.endsWith("Map") || type.endsWith("SparseArray")){
            return true;
        }
        return false;
    }

    public static boolean isListValue(Value v){
        if(v==null) return false;
        String type = v.getType().toString();
        if(type.endsWith("List")){
            return true;
        }
        return false;
    }

    public static boolean hasMapValue(List<Value> values){
        if(values == null) return false;
        for(Value v : values){
            if(isMapValue(v)){
                return true;
            }
        }
        return false;
    }

    public static boolean isNumeric(String s){
        Pattern pattern = Pattern.compile("[0-9]*");
        Matcher isNum = pattern.matcher(s);
        if(isNum.matches()) return true;
        return false;
    }

    public static boolean isExpress(String str){
        char[] ops = {'&', '|', '!','+', '-', '*', '/', '%', '^'};
        for(char op : ops){
            if(str.contains(String.valueOf(op))) return true;
        }
        return false;
    }

    public static boolean hasDuplicatedItems(List<List<Integer>> paths){
        long count = paths.stream().distinct().count();
        if(count == paths.size()){
            return false;
        }else{
            return true;
        }
    }

    public static boolean isNewStmt(AssignStmt as){
        if(as == null) return false;

        if(as.getUseBoxes().size() == 1 && as.getRightOp().toString().startsWith("new")) {
            return true;
        }
        return false;
    }

    public static int isParamStmt(IdentityStmt is){
        if(is == null) return -1;

        String s = is.getRightOp().toString();
        if (s.contains("@parameter")) {
            int index = s.indexOf("@parameter");
            return Character.getNumericValue(s.charAt(index + 10));
        }
        return -1;
    }

    public static boolean areRelatedNames(String name, String method_name){
        method_name = method_name.toLowerCase();
        return method_name.contains(name);
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

    public static List<Unit> bodyToList(Body body){
        List<Unit> b = new ArrayList<>();
        if(body==null) return b;
        for(Unit unit : body.getUnits()){
            b.add(unit);
        }
        return b;
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

    public static void initializeInterfaceClassesInfo(){
        for(SootClass cls : Scene.v().getClasses()){
            for (SootClass interface_class : cls.getInterfaces()) {
                if(cls.isInterface()){
                    Set<SootClass> extended_classes = interfaceClassToSubInterfaceClasses.get(interface_class);
                    if(extended_classes==null){
                        extended_classes = new HashSet<>();
                        extended_classes.add(cls);
                        interfaceClassToSubInterfaceClasses.put(interface_class, extended_classes);
                    } else {
                        extended_classes.add(cls);
                    }
                } else {
                    Set<SootClass> implemented_classes = interfaceClassToImplementedClasses.get(interface_class);
                    if (implemented_classes == null) {
                        implemented_classes = new HashSet<>();
                        implemented_classes.add(cls);
                        interfaceClassToImplementedClasses.put(interface_class, implemented_classes);
                    } else {
                        implemented_classes.add(cls);
                    }
                }
            }

        }
    }

    public static <T> Set<T> deepCopy(Set<T> src){
        Set<T> dest = new HashSet<>();
        if(src==null){
            return dest;
        }
        for(T object : src){
            dest.add(object);
        }
        return dest;
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

    public static <K, V> Map<K, V> deepCopy(Map<K, V> src) {
        Map<K, V> dest = new HashMap<K, V>();
        if(src == null){
            return dest;
        }
        for(Map.Entry<K, V> entry : src.entrySet()){
            dest.put(entry.getKey(), entry.getValue());
        }
        return dest;
    }

    public static void pause(){
        try{
            System.out.println("Enter anything to continue ...");
            char in = (char) System.in.read();
        } catch (IOException e){
            e.printStackTrace();
        }
    }

    public static void createDir(String dir_path){
        try {
            File dir = new File(dir_path);
            if (!dir.exists()) {
                dir.mkdirs();
            }
        }catch (Exception e){
            throw new RuntimeException(e);
        }
    }

    public static void copyFile(File source, String dest_path){
        try {
            File dest = new File(dest_path);
            createDir(dest.getParent());
            FileChannel inputChannel = new FileInputStream(source).getChannel();
            FileChannel outputChannel = new FileOutputStream(dest).getChannel();
            outputChannel.transferFrom(inputChannel, 0, inputChannel.size());
            inputChannel.close();
            outputChannel.close();
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static String ms2DHMS(long start, long end){
        String retval = null;
        long secondCount = (end-start) / 1000;
        String ms = (end - start) % 1000 + "ms";

        long days = secondCount / (60*60*24);
        long hours = (secondCount % (60*60*24)) / (60*60);
        long minutes = (secondCount % (60*60)) / 60;
        long seconds = secondCount % 60;

        if(days > 0){
            retval = days + "d" + hours + "h" + minutes + "m" + seconds + "s";
        } else if (hours > 0) {
            retval = hours + "h" + minutes + "m" + seconds + "s";
        } else if (minutes > 0) {
            retval = minutes + "m" + seconds + "s";
        } else if (seconds > 0) {
            retval = seconds + "s";
        } else {
            return ms;
        }
        return retval + ms;
    }
}


