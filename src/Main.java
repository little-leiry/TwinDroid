import analysis.*;
import comparator.VBComparator;
import soot.*;

import soot.jimple.*;
import soot.options.Options;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.io.*;
import java.util.*;

import static java.lang.Thread.sleep;

public class Main {
    public static final String base_path_12 = "/data/disk_16t_2/leiry/android12_source/";
    public static final String dexCode_path_12 = base_path_12 + "DEX-12-framework/";
    public static final String dexCode_path_lite_12 = base_path_12 + "systemCode/";
    public static final String javaCode_path_12 = base_path_12 + "javaCode/";
    public static final String classCode_path_12 = base_path_12 + "classCode/";
    public static final String sourceCode_base_path = base_path_12 + "android12/";

    public static final String base_path_11 = "/data/disk_16t_2/leiry/android11_source/";
    public static final String dexCode_path_11 = base_path_11 + "DEX-11-framework/";

    public static List<String> call_path = new ArrayList<>();
    public static List<List<String>> call_paths = new ArrayList<>();
    public static Map<String, List<String>> methodToParents = new HashMap<String, List<String>>();

    public static void main(String[] args) throws IOException, InterruptedException {
        long start, end;
        Utils.printPartingLine("+");
        start = System.currentTimeMillis();
        System.out.println("Initializing classes...");
        sootInitial_dex(dexCode_path_12);
        System.out.println("Done.");
        Utils.printPartingLine("+");
        System.out.println("Initializing interface classes information...");
        Utils.initializeInterfaceClassesInfo();
        System.out.println("Done");
        end = System.currentTimeMillis();
        System.out.println("Initialization: " + Utils.ms2DHMS(start, end));
        Utils.printPartingLine("+");
        /*start = System.currentTimeMillis();
        AnalysisForParsingClass2.findSuspiciousDataStructures();
        end = System.currentTimeMillis();
        System.out.println("Stage 1: " + Utils.ms2DHMS(start, end));
        start = System.currentTimeMillis();
        AnalysisForUsingMethods.findSuspiciousMethods();
        end = System.currentTimeMillis();
        System.out.println("Stage 2: " + Utils.ms2DHMS(start, end));*/
        test3();
    }

    private static void sootInitial_dex(String code_path) {
        soot.G.reset();
        // android.jar包位置
        Options.v().set_force_android_jar("lib/android31.jar");
        // 处理java则为Options.src_prec_java，处理jar包则为src_prec_J
        Options.v().set_src_prec(Options.src_prec_apk);
        // 该处测试用于apk，可注释
        Options.v().set_process_multiple_dex(true);
        // 以下不用管
        Options.v().set_process_dir(Collections.singletonList(code_path));
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().ignore_resolution_errors();
        Scene.v().loadNecessaryClasses();
    }

    private static void sootInitial_java(String javaPath) {
        soot.G.reset();
        // android.jar包位置
        Options.v().set_force_android_jar("lib/android31.jar");
        Options.v().set_src_prec(Options.src_prec_class);
        // 以下不用管
        Options.v().set_process_dir(Collections.singletonList(javaPath));
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().ignore_resolution_errors();
        Scene.v().loadNecessaryClasses();
    }

    // analyse test.javad
    private static void test() {

    }

    public static void test1(){
        long start, end;
        start = System.currentTimeMillis();
        List<String > a = new ArrayList<>();
        a.add("1");
        String[] b = new String[1];
        b[0] = "2";
        for(String s : b){
            System.out.println(s);
        }
        a.toArray(b);
        for(String s : b){
            System.out.println(s);
        }
        end = System.currentTimeMillis();
        System.out.println(end-start);
    }

    // print body
    // given class name and method name
    public static void test2() {
        String[] className = {
                "com.android.server.pm.permission.PermissionManagerService",
                "android.content.pm.parsing.component.ParsedInstrumentation",
                "com.android.server.pm.SharedUserSetting",
                "androidx.appcompat.widget.SuggestionsAdapter",
                "android.content.pm.parsing.ParsingPackageImpl",
                "com.android.server.pm.PackageManagerService",
                "android.content.pm.parsing.component.ParsedComponent",
                "com.android.server.pm.parsing.pkg.PackageImpl",
                "android.content.res.XmlBlock",
                "android.content.pm.parsing.ParsingPackage",
                "android.content.pm.parsing.PackageInfoWithoutStateUtils",
                "com.android.server.pm.parsing",
                "com.android.server.backup.UserBackupManagerService"
        };
        String[] methodName = {"revokeRuntimePermissionsIfGroupChanged", "<init>", "getActivities", "addActivity", "preparePackageLI", "newParser", "revokeRuntimePermissionsIfGroupChangedInternal",
        "generateWithComponents", "PackageParserLegacyCoreTest", "addPackage", "readFullBackupSchedule"};
        /*SootClass cls = Scene.v().getSootClassUnsafe(className[0]);
        System.out.println(cls.getInterfaces());
        System.out.println(cls.getSuperclass().isAbstract());*/
        List<Body> bodies = Utils.getBodyOfMethod(className[0], methodName[0]);
        for(Body b : bodies){
            //System.out.println(b);
            for(Unit u: b.getUnits()){
                if(u instanceof AssignStmt){
                    AssignStmt as = (AssignStmt) u;
                    InvokeExpr ie = analysis.Utils.getInvokeOfAssignStmt(as);
                    if(ie!=null && ie.getMethod().getName().equals("getPermissions")){
                        System.out.println(ie);
                        if(ie instanceof InterfaceInvokeExpr){
                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                            System.out.println(Analysis.getImplementedMethodOfAbstractMethod(null, ifi, null));
                        }
                    }
                }
            }
        }
    }

    // print body
    // given method signature
    private static void test3() {
        String[] sigs = {
                "<android.content.pm.parsing.component.ParsedProcessUtils: android.content.pm.parsing.result.ParseResult parseProcess(java.util.Set,java.lang.String[],android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.component.ParsedAttributionUtils: android.content.pm.parsing.result.ParseResult parseAttribution(android.content.res.Resources,android.content.res.XmlResourceParser,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseUsesFeature(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<com.android.server.pm.AppsFilter: boolean canQueryViaPackage(com.android.server.pm.parsing.pkg.AndroidPackage,com.android.server.pm.parsing.pkg.AndroidPackage)>",
                "<android.content.pm.PackageManager: android.content.pm.PackageInfo getPackageInfoAsUser(java.lang.String,int,int)>",
                "<com.android.server.pm.permission.PermissionManagerService: void onPackageAddedInternal(com.android.server.pm.parsing.pkg.AndroidPackage,boolean,com.android.server.pm.parsing.pkg.AndroidPackage)>",
                "<com.android.server.pm.permission.PermissionManagerService: void grantRuntimePermissionInternal(java.lang.String,java.lang.String,boolean,int,int,com.android.server.pm.permission.PermissionManagerService$PermissionCallback)>",
                "<android.content.pm.parsing.component.ParsedProcessUtils: android.content.pm.parsing.result.ParseResult parseProcesses(java.lang.String[],android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int,android.content.pm.parsing.result.ParseInput)>"
        };
        String methodSig = sigs[0];
        Body body = Utils.getBodyOfMethod(methodSig);
        //System.out.println(body);
        //List<Value> values = new ArrayList<>();
        //Value v = null;
        //System.out.println(body);
        //UnitGraph ug = new ExceptionalUnitGraph(body);
        /*UnitGraph ug = new CompleteUnitGraph(body);
        test.TestImpl test = new test.TestImpl(ug);
        Unit unit = ug.getHeads().get(0);
        while(true){
            System.out.println(unit);
            System.out.println(test.getFlowAfter(unit));
            System.out.println(test.getFlowBefore(unit));
            unit = body.getUnits().getSuccOf(unit);
            if(unit == null) break;
            analysis.Utils.pause();
        }*/
        /*CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        List<Block> blocks = new ArrayList<>();
       *//* List<Integer> ancestor = new ArrayList<>();
        Graph.getAncestorsOfBlock(cbg.getBlocks().get(19), ancestor);
        System.out.println(ancestor);
        for (int i = 2; i < 20; i+=4) {
            blocks.add(cbg.getBlocks().get(i));
        }*//*
        blocks.add(cbg.getBlocks().get(8));
        blocks.add(cbg.getBlocks().get(18));
        blocks.add(cbg.getBlocks().get(23));
        *//*blocks.add(cbg.getBlocks().get(39));
        blocks.add(cbg.getBlocks().get(52));
        blocks.add(cbg.getBlocks().get(61));
        blocks.add(cbg.getBlocks().get(73));
        blocks.add(cbg.getBlocks().get(76));
        blocks.add(cbg.getBlocks().get(86));
        blocks.add(cbg.getBlocks().get(91));
        blocks.add(cbg.getBlocks().get(93));
        blocks.add(cbg.getBlocks().get(96));
        blocks.add(cbg.getBlocks().get(102));
        blocks.add(cbg.getBlocks().get(115));
        blocks.add(cbg.getBlocks().get(129));
        blocks.add(cbg.getBlocks().get(142));
        blocks.add(cbg.getBlocks().get(163));
        blocks.add(cbg.getBlocks().get(184));
        blocks.add(cbg.getBlocks().get(197));
        blocks.add(cbg.getBlocks().get(209));*//*
        System.out.println("Stupid: " + Graph.getLeastCommonAncestorOfBlocks2(blocks));
        System.out.println("Smart: " + Graph.getLeastCommonAncestorOfBlocks(blocks));*/
        //Block block = cbg.getBlocks().get(71);
        //System.out.println(Graph.isTailBlockOfLoop(block));
        /*Collection<ExceptionalBlockGraph.ExceptionDest> exceptionDests = cbg.getExceptionDests(block);
        System.out.println(exceptionDests.size());
        for(ExceptionalBlockGraph.ExceptionDest e : exceptionDests){
            System.out.println(e.getHandlerNode());
            System.out.println(e.getThrowables());
        }*/

       for(Unit unit : body.getUnits()) {
           if(unit instanceof AssignStmt){
               AssignStmt as = (AssignStmt) unit;
               if(Analysis.isIdentifierRelated(as, "parseAttribution")){
                   System.out.println("===: " + as);
               }
           }
       }
    }


    private static void test4() {
        Set<String> s1 = new HashSet<>();
        s1.add("A");
        List<String> t1 = new ArrayList<>(s1);
        t1.remove(0);
        System.out.println(s1);
        System.out.println(t1);
        BU a = new BU();

        /*String element1 = "[[\"application\"_\"library\"]]";
        System.out.println(AnalysisForUsingMethods.isDeDuplicateMethod(element1));
        String element2 = "[[\"application\"_\"uses-library\"], [\"application\"_\"uses-static-library\"], [\"application\"_\"uses-native-library\"]]";
        System.out.println(AnalysisForUsingMethods.isDeDuplicateMethod(element2));
        String element3 = "[[\"application\"_\"uses-permission-sdk-m\", \"application\"_\"uses-permission\", \"application\"_\"uses-permission-sdk-23\"]]";
        System.out.println(AnalysisForUsingMethods.isDeDuplicateMethod(element3));
        String element4 = "[[\"application\"_\"uses-permission-sdk-m\", \"application\"_\"uses-permission\", \"application\"_\"uses-permission-sdk-23\"], [\"application\"_\"uses-static-library\"], [\"application\"_\"library\"]]";
        System.out.println(AnalysisForUsingMethods.isDeDuplicateMethod(element4));
        String element5 = "[[\"application\"_\"instrumentation\"], [\"application\"_\"library\"]]";
        System.out.println(AnalysisForUsingMethods.isDeDuplicateMethod(element5));
        String e6 = "[[\"application\"_\"receiver\"], [\"application\"_\"activity\", \"application\"_\"activity-alias\"], [\"application\"_\"provider\"], [\"application\"_\"service\"]]";
        System.out.println(AnalysisForUsingMethods.isDeDuplicateMethod(e6));*/
    }

    public static void test5() throws IOException, InterruptedException {
        String framework_path = sourceCode_base_path+"frameworks";
        String packages_path = sourceCode_base_path+"packages";
        getJavaFiles(packages_path);
        //copyFile(new File("src/analysis.Log.java"), "Log_copy.java");
        //File f = new File("src/analysis.Log.java");
        //System.out.println(f.getParent());
        //createDir("/data/disk_16t_2/leiry/1/2/3");
    }

    public static void test6(){
        /*List<String> data = Log.readData(AnalysisForParsingClass.analysis_data);
        Set<String> methods = new HashSet<>();
        for(int i= 0; i< data.size(); i++){
            if(data.get(i).equals("--- analysis.Tainted callee.")){
                int j = i;
                while(true){
                    j = j -1;
                    if(data.get(j).startsWith("+ Unit:")){
                        String method = data.get(j).split(".<")[1].split(">")[0];
                        //System.out.println(method);
                        methods.add(method);
                        //analysis.Utils.pause();
                        break;
                    }
                }
            }
        }
        for(String method : methods){
            System.out.println(method);
        }*/
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("js");
        String express = "0 != null";
        try {
            boolean result = (boolean) se.eval(express);
            System.out.println(result);
        } catch (ScriptException e) {
            throw new RuntimeException(e);
        }
    }


    public static void getJavaFiles(String file_path){
        //System.out.println(file_path);
        if(file_path == null) return;
        File file = new File(file_path);
        if (file.isFile()) {
            if (file.getName().endsWith(".java")) {
                String dest_path = file.getAbsolutePath().replace(sourceCode_base_path, javaCode_path_12);
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

    public static void generateCallPaths(String method_sig, int flag, int depth){
        System.out.println("-----------------------------");
        System.out.println("depth: " + depth);
        System.out.println("flag: " + flag);
        if(flag == 0 && depth == 1){
            System.out.println("Ok");
            flag =1;
        }
        call_path.add(method_sig);
        if(methodToParents.containsKey(method_sig)){
            List<String> parents = methodToParents.get(method_sig);
            depth += 1;
            for(String p : parents){
                System.out.println("method: " + method_sig + " => " + " parent: " + p);
                generateCallPaths(p, flag, depth);
            }
            call_path.remove(method_sig);
        }else{
            System.out.println("method: " + method_sig + " => " + " No parent.");
            System.out.println(call_path);
            List<String> call_path_copy = new ArrayList<>();
            for(int i = call_path.size(); i > 0; i--){
                call_path_copy.add(call_path.get(i-1));
            }
            call_paths.add(call_path_copy);
            System.out.println(call_paths);
            call_path.remove(method_sig);
        }
    }

    public static void createOrUpdateValueToLikelyElement(AssignStmt as, Map<Value, String> valueToLikelyElement){
        List<ValueBox> vbs = as.getUseBoxes();
        if (vbs.size()==1 && vbs.get(0).getValue() instanceof StringConstant) {
            Value element_value = as.getLeftOp();
            String likely_element = as.getUseBoxes().get(0).getValue().toString();
            if(likely_element.startsWith("\"/")) return;
            valueToLikelyElement.put(element_value, likely_element);
            Utils.printPartingLine("+");
            System.out.println("Likely element: " + as);
            Utils.printPartingLine("+");
        }
    }

    public static void constructNumericValueToConcreteValue(AssignStmt as, Map<Value, String> byteValueToConcreteValue){
        Value def_value = as.getLeftOp();
        String def_value_type = def_value.getType().toString();
        if("byte_int_boolean".contains(def_value_type)){
            //System.out.println(as);
            //System.out.println("====: " + as.getDefBoxes());
            //System.out.println("====: " + def_value);
            //System.out.println("++++: " + as.getUseBoxes());
            //System.out.println("&&&&: " + as.getRightOp());
           // Value vv = as.getUseBoxes().get(0).getValue();
            //System.out.println("****: " + analysis.Utils.isRightValueOfAssignment(as, vv));
            if(as.getUseBoxes().size() == 1){
                Value use_value = as.getRightOp();
                if(use_value instanceof IntConstant){
                    System.out.println("int: " + as);
                    byteValueToConcreteValue.put(def_value, use_value.toString());
                    System.out.println(def_value + " => " + use_value.toString());
                } else {
                    String assignment = byteValueToConcreteValue.get(use_value);
                    if(assignment!=null) {
                        byteValueToConcreteValue.put(def_value, assignment);
                        System.out.println("++++: " + def_value + " => " + assignment);
                    } else {
                        System.out.println("wrong.");
                    }
                }
            } else if (as.getUseBoxes().size() == 2){
                System.out.println("---: " + as.getUseBoxes());
                if(as.getUseBoxes().get(0).getValue().toString().startsWith("(")){
                    String assign = byteValueToConcreteValue.get(as.getUseBoxes().get(1).getValue());
                    byteValueToConcreteValue.put(def_value, assign);
                } else {
                    System.out.println("Special assignment (not the type transformation): " + as);
                }
            }else{
                System.out.println("Special assignment of a byte value: " + as);
                List<ValueBox> vbs = as.getUseBoxes();
                Collections.sort(vbs, new VBComparator());
                String s = vbs.get(0).getValue().toString();
                int flag_compute = 1;
                if(Utils.isExpress(s)){
                    for(int j = 1; j<vbs.size(); j++){
                        Value v = vbs.get(j).getValue();
                        String assign = byteValueToConcreteValue.get(v);
                        if(assign == null){
                            flag_compute = 0;
                            byteValueToConcreteValue.put(def_value, null);
                            break;
                        }
                        s = s.replace(v.toString(), assign);
                    }
                    System.out.println(s);
                    if(flag_compute == 1) {
                        ScriptEngineManager sem = new ScriptEngineManager();
                        ScriptEngine se = sem.getEngineByName("js");
                        Object result = null;
                        try {
                            result = se.eval(s);
                            System.out.println("result: " + result);
                        } catch (ScriptException e) {
                            throw new RuntimeException(e);
                        }
                        byteValueToConcreteValue.put(def_value, result.toString());
                        System.out.println("++++: " + def_value + " => " + result.toString());
                    }
                } else {
                    System.out.println("!!! Not an express.");
                }
            }
        }
        return;
    }
}

