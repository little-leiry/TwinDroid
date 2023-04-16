package analysis;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.Block;

import java.io.*;
import java.nio.channels.FileChannel;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static java.lang.System.exit;
import static java.lang.System.out;

public class Utils {
    public static final String code_base_path_12 = "/data/disk_16t_2/leiry/android12_source/";
    public static final String javaCode_path_12 = code_base_path_12 + "javaCode/";
    public static final String classCode_path_12 = code_base_path_12 + "classCode/";

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

    public static <T> List<T> deepCopy(List<T> src) {
        if(src == null){
            return new ArrayList<>();
        }
        return new ArrayList<>(src);
    }

    public static <K, V> Map<K, V> deepCopy(Map<K, V> src) {
        if(src == null){
            return new HashMap<K, V>();
        }
        return new HashMap<>(src);
    }

    public static <T> Set<T> deepCopy(Set<T> src){
        if(src==null){
            return new HashSet<>();
        }
        return new HashSet<>(src);
    }

    public static void getJavaFiles(String file_path){
        //System.out.println(file_path);
        if(file_path == null) return;
        File file = new File(file_path);
        if (file.isFile()) {
            if (file.getName().endsWith(".java")) {
                String dest_path = file.getAbsolutePath().replace(code_base_path_12, javaCode_path_12);
                System.out.println(dest_path);
                Utils.copyFile(file, dest_path);
            }
        } else if (file.isDirectory()) {
            File[] files = file.listFiles();
            for (File f : files) {
                getJavaFiles(f.getAbsolutePath());
            }
        }
    }

    public static String generatePartingLine(String symbol){
        String s = "";
        for(int i = 0; i<100;i++){
            s+=symbol;
        }
        return s;
    }

    // r1[i1] => r1
    public static Value getArrayVariable(Value v){
        if(v.toString().contains("[") && v.getUseBoxes().size() == 2){
            v = v.getUseBoxes().get(0).getValue();
        }
        return v;
    }

    public static Value getBaseOfInvokeExpr(InvokeExpr ie){
        if(ie==null) return null;

        if (ie instanceof VirtualInvokeExpr) {
            return ((VirtualInvokeExpr) ie).getBase();
        } else if (ie instanceof InterfaceInvokeExpr) {
            return ((InterfaceInvokeExpr) ie).getBase();
        } else if (ie instanceof SpecialInvokeExpr) {
            return ((SpecialInvokeExpr) ie).getBase();
        }
        return null;
    }

    public static Value getBaseVariable(Value v){
        if(!v.getUseBoxes().isEmpty()){
            v = v.getUseBoxes().get(0).getValue();
        }
        return v;
    }

    public static String getBlockIds (List<Block> blocks){
        if(blocks == null || blocks.isEmpty()) return null;

        String s = "";
        for(Block b : blocks){
            s += b.getIndexInMethod() + "_";
        }
        return s;
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

    public static String getCalleeName(InvokeExpr callee) {
        return callee.getMethod().getName();
    }

    public static String getCalleeSig(InvokeExpr callee) {
        return callee.getMethod().getSignature();
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

    public static SootClass getDeclaringClassOfArrayElement(ArrayType array_type){
        if(array_type == null) return null;

        Type array_element_type = array_type.getArrayElementType();
        while(array_element_type instanceof ArrayType){ // A[][]
            ArrayType element_at = (ArrayType) array_element_type;
            array_element_type = element_at.getArrayElementType();
        }
        String declaring_class_name = array_element_type.toString();
        SootClass declaring_class = Scene.v().getSootClassUnsafe(declaring_class_name);
        return declaring_class;
    }

    // $z0 = <android.content.pm.parsing.ParsingPackageUtils: boolean sUseRoundIcon>;
    // r17 = r0.<android.content.pm.parsing.ParsingPackageUtils: java.lang.String[] mSeparateProcesses>;
    public static String getFieldNameFromAssignStmt(AssignStmt as){
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(ie!=null) return null;
        Value right_op = as.getRightOp();
        if(isFieldVariable(right_op)){
            String field = "<" + right_op.toString().split("<")[1];
            return field;
        }
        return null;
    }

    public static int getIndexOfUnit(Body body, Unit unit){
        if(body==null || unit == null) return -1;
        return bodyToList(body).indexOf(unit);
    }

    public static InvokeExpr getInvokeOfAssignStmt(AssignStmt as) {
        if(as==null) return null;
        if (as.containsInvokeExpr()) {
            InvokeExpr invoke = as.getInvokeExpr();
            return invoke;
        }
        return null;
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

    public static List<SootMethod> getMethodsOfClass(String className) {
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        if (cls == null) { // the given class is not exist
            return null;
        }
        return cls.getMethods();
    }

    public static Value getParameterOfMethodByIndex(Body body, Integer parameter_index) {
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

    public static Value getParamByIndex(Map<Value, Integer> paramToIndex, int index){
        if(paramToIndex == null) return null;

        for(Map.Entry<Value, Integer> entry : paramToIndex.entrySet()){
            Value param = entry.getKey();
            int param_index = entry.getValue();
            if(index == param_index){
                return param;
            }
        }
        return null;
    }

    public static Value getReturnVariable(Body body){
        if(body == null) return null;

        for(Unit unit : body.getUnits()){
            if(unit instanceof ReturnStmt) {
                Value return_variable = ((ReturnStmt) unit).getOp();
                if (!(return_variable instanceof NullConstant)){ // return null;
                    return return_variable;
                }
            }
        }
        return null;
    }



    public static Set<SootClass> getSuperClasses(SootClass cls) {
        Set<SootClass> super_classes = new HashSet<>();
        if (cls == null) {
            return super_classes;
        }
        while (cls.hasSuperclass()) {
            cls = cls.getSuperclass();
            super_classes.add(cls);
        }
        return super_classes;
    }

    public static void javaFileToClassFile(String file_path){
        try{
            File file = new File(file_path);
            if(file.isFile()){
                if(!file_path.endsWith(".java")) return;
                String dest_dir_path = file.getParent().replace(javaCode_path_12, classCode_path_12);
                Runtime.getRuntime().exec("javac -d " + dest_dir_path + " " + file_path);
            } else if(file.isDirectory()){
                File[] files = file.listFiles();
                for(File f : files){
                    javaFileToClassFile(f.getAbsolutePath());
                }
            }
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

    public static void logMsg(String log_file, String msg, String symbol){
        Log.logData(log_file, generatePartingLine(symbol));
        Log.logData(log_file, msg);
        Log.logData(log_file, generatePartingLine(symbol));
    }

    public static void printMsg(String msg, String symbol){
        out.println(generatePartingLine(symbol));
        out.println(msg);
        out.println(generatePartingLine(symbol));
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

    public static void pause(){
        try{
            System.out.println("Enter anything to continue ...");
            char in = (char) System.in.read();
        } catch (IOException e){
            e.printStackTrace();
        }
    }

    public static void terminate(String msg){
        printPartingLine("!");
        System.out.println(msg);
        printPartingLine("!");
        exit(0);
    }

    public static boolean isArrayVariable(Value v){
        if(v==null) return false;

        if(v.getType().toString().contains("[]")){
            return true;
        }
        return false;
    }

    public static boolean isCopyStmt(AssignStmt as){
        if(as == null) return false;
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(ie == null && as.getUseBoxes().size() == 1){ // r1 = r2
            String right_value_type = as.getRightOp().getType().toString();
            String left_value_type = as.getLeftOp().getType().toString();
            if(right_value_type.equals(left_value_type)){ // r1's type == r2's type
                return true;
            }
        }
        return false;
    }

    // r7 = r4
    // r7 is a copy of r4
    public static boolean isCopyOfVariable(AssignStmt as, Value v){
        if(as==null || v == null) return false;
        InvokeExpr ie = getInvokeOfAssignStmt(as);
        List<ValueBox> vbs = as.getUseBoxes();
        v = getArrayVariable(v);
        // There is a copy of value.
        if(vbs.size()==1 && ie == null){
            Value right_value = as.getRightOp();
            Value left_value = as.getLeftOp();
            if(v.equals(right_value) &&
                    v.getType().equals(left_value.getType())){
                return true;
            }
        }
        return false;
    }

    public static boolean hasCopyOfVars(AssignStmt as, List<Value> vars){
        if(as==null || vars == null) return false;
        for(Value v : vars){
            if(isCopyOfVariable(as, v) == true) return true;
        }
        return false;
    }

    public static boolean isDuplicationVariable(Value v){
        if(v==null) return false;
        v = Utils.getArrayVariable(v);
        String type = v.getType().toString();
        if(type.endsWith("List") || type.endsWith("[]") || type.endsWith("Queue") || type.endsWith("Stack")){
            return true;
        }
        return false;
    }

    public static boolean isDuplicationField(SootField f){
        if(f==null) return false;

        String type = f.getType().toString();
        if(type.endsWith("List") || type.endsWith("[]") || type.endsWith("Queue") || type.endsWith("Stack")){
            return true;
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

    public static boolean isExpress(String str){
        char[] ops = {'&', '|', '!','+', '-', '*', '/', '%', '^'};
        for(char op : ops){
            if(str.contains(String.valueOf(op))) return true;
        }
        return false;
    }

    public static boolean isFieldVariable(Value v){
        if(v==null) return false;

        if(v.toString().contains("<") && v.toString().endsWith(">") && v.getUseBoxes().size() <= 1){
            return true;
        }
        if(v.toString().contains("<") && !v.toString().contains("<<") && !(v instanceof StringConstant)){
            out.println("&&&&& " + v);
        }

        return false;
    }

    public static boolean isFieldOfClass(Value var, SootClass cls){
        if(var == null || cls == null) return false;

        if(!isFieldVariable(var)) return false;

        String field = "<" + var.toString().split("<")[1];
        for(SootField sf : cls.getFields()){
            if(sf.getSignature().equals(field)){
                return true;
            }
        }
        return false;
    }

    public static boolean isMapVariable(Value v){
        if(v==null) return false;
        String type = v.getType().toString();
        if(type.endsWith("Map") || type.endsWith("SparseArray")){
            return true;
        }
        return false;
    }

    public static boolean isMapField(SootField f){
        if(f==null) return false;

        String type = f.getType().toString();
        if(type.endsWith("Map") || type.endsWith("SparseArray")){
            return true;
        }
        return false;
    }

    public static boolean hasMapVariable(List<Value> vars){
        if(vars == null) return false;
        for(Value v : vars){
            if(isMapVariable(v)){
                return true;
            }
        }
        return false;
    }

    public static boolean isNewStmt(AssignStmt as){
        if(as == null) return false;

        if(as.getUseBoxes().size() == 1 && as.getRightOp().toString().startsWith("new")) {
            return true;
        }
        return false;
    }

    public static boolean isNumeric(String s){
        Pattern pattern = Pattern.compile("[0-9]*");
        Matcher isNum = pattern.matcher(s);
        if(isNum.matches()) return true;
        return false;
    }

    public static boolean isNumericVariable(Value v){
        if(v==null) return false;
        if("int_byte_boolean".contains(v.getType().toString())){
            return true;
        }
        return false;
    }

    public static boolean isOneDimensionArray(Value v){
        String type = v.getType().toString();
        if(type.endsWith("[]") && !type.contains("][")){
            return true;
        }
        return false;
    }

    public static boolean isPairVariable(Value v){
        if(v==null) return false;
        String type = v.getType().toString();
        if(type.endsWith("Pair")){
            return true;
        }
        return false;
    }

    public static int isParamStmt(IdentityStmt is){
        if(is == null) return -1;

        String s = is.getRightOp().toString();
        if (s.contains("@parameter")) {
            String index = s.split("@parameter")[1].split(":")[0];
            return Integer.parseInt(index);
        }
        return -1;
    }

    public static boolean isSetVariable(Value v){
        if(v==null) return false;
        String type = v.getType().toString();
        if(type.endsWith("Set")){
            return true;
        }
        return false;
    }

    public static boolean isStructuralVariable(Value v){
        if(isMapVariable(v) || isDuplicationVariable(v) || isPairVariable(v) || isSetVariable(v)){
            return true;
        }
        return false;
    }

    public static boolean isStringVariable(Value v){
        if(v==null) return false;

        String type = v.getType().toString();
        if(type.endsWith("String")) {
            return true;
        }
        return false;
    }

    public static <K, V> boolean areMapValuesNull(Map<K, V> map) {
        if(map == null) return true;

        for(V value : map.values()) {
            if(!value.equals(null)){
                return false;
            }
        }
        return true;
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
}


