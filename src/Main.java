import soot.*;

import soot.jimple.*;
import soot.options.Options;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.io.*;
import java.nio.channels.FileChannel;
import java.util.*;

import static java.lang.Thread.sleep;

public class Main {
    public static final String base_path = "/data/disk_16t_2/leiry/";
    public static final String sourceCode_base_path = base_path + "android12/";
    public static final String dexCode_path = base_path + "systemCode/";
    public static final String javaCode_path = base_path + "javaCode/";
    public static final String classCode_path = base_path + "classCode/";
    public static final String path_test = base_path + "useful_file";

    public static List<String> call_path = new ArrayList<>();
    public static List<List<String>> call_paths = new ArrayList<>();
    public static Map<String, List<String>> methodToParents = new HashMap<String, List<String>>();

    public static void main(String[] args) throws IOException, InterruptedException {
        Utils.printPartingLine("+");
        System.out.println("Initializing...");
        //sootInitial_java(classCode_path);
        sootInitial_dex(dexCode_path);
        System.out.println("Done.");
        Utils.printPartingLine("+");
        Utils.initializeInterfaceClassesInfo();
        //test3();
        //javaFileToClassFile(javaCode_path);
        //findEntries();
        AnalysisForParsingClass.findSuspiciousDataStructures();
        //AnalysisForUsingMethods.findSuspiciousMethods();
        //AnalysisForUsingMethods.getEntries();
        /*ElementInfo test = new ElementInfo();
        test6(test);
        System.out.println(test.getCaseNum());
        System.out.println(test.getCaseIdToElement());*/
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
        sootInitial_java(dexCode_path);
        //SootClass cls =Scene.v().getSootClassUnsafe("test");
        /*for(SootMethod sm : cls.getMethods()){
            *//*for(Unit unit: sm.retrieveActiveBody().getUnits()){
                if(unit instanceof InvokeStmt){
                    InvokeExpr i = ((InvokeStmt) unit).getInvokeExpr();
                }
            }*//*
            System.out.println(sm.getDeclaringClass());
        }*/
    }

    public static void test1(){
    }

    // print body
    // given class name and method name
    public static void test2() {
        String[] className = {
                "com.android.server.pm.SharedUserSetting",
                "androidx.appcompat.widget.SuggestionsAdapter",
                "android.content.pm.parsing.ParsingPackageImpl",
                "com.android.server.pm.PackageManagerService",
                "android.content.pm.parsing.component.ParsedComponent",
                "com.android.server.pm.parsing.pkg.PackageImpl",
                "android.content.res.XmlBlock",
                "com.android.server.pm.permission.PermissionManagerService",
                "android.content.pm.parsing.ParsingPackage",
                "android.content.pm.parsing.PackageInfoWithoutStateUtils",
                "com.android.server.pm.parsing"
        };
        String[] methodName = {"getActivities", "addActivity", "preparePackageLI", "newParser", "revokeRuntimePermissionsIfGroupChangedInternal",
        "generateWithComponents", "PackageParserLegacyCoreTest", "addPackage"};
        /*SootClass cls = Scene.v().getSootClassUnsafe(className[0]);
        Map<String, String> entryToElement = AnalysisForUsingMethods.getEntries();
        AnalysisForUsingMethods.test(cls, entryToElement);*/
        //System.out.println(cls.getInterfaces());
        List<Body> bodies = Utils.getBodyOfMethod(className[0], methodName[7]);
        for(Body b : bodies){
            System.out.println(b);
            /*for(Unit u: b.getUnits()){
                if(u instanceof AssignStmt){
                    AssignStmt as = (AssignStmt) u;
                    InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                    if(ie!=null && ie.getMethod().getName().equals("getActivities")){
                        System.out.println(ie);
                        if(ie instanceof InterfaceInvokeExpr){
                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                            SootMethod method = AnalysisForUsingMethods.getImplementedMethodOfAbstractMethod(null, ifi, null);
                            System.out.println(method);
                            break;
                        }
                    }
                }
            }*/
        }
    }

    // print body
    // given method signature
    private static void test3() {
        String[] sigs = {
                "<android.content.pm.parsing.PackageInfoWithoutStateUtils: android.content.pm.PackageInfo generateWithoutComponentsUnchecked(android.content.pm.parsing.ParsingPackageRead,int[],int,long,long,java.util.Set,android.content.pm.PackageUserState,int,android.apex.ApexInfo,android.content.pm.ApplicationInfo)>",
                "<com.android.server.pm.AppsFilter: void lambda$removePackage$7$AppsFilter(com.android.server.pm.PackageSetting,android.util.ArrayMap,android.content.pm.UserInfo[])>",
                "<android.widget.RemoteViews$BaseReflectionAction: void apply(android.view.View,android.view.ViewGroup,android.widget.RemoteViews$InteractionHandler,android.widget.RemoteViews$ColorResources)>",
                "<com.android.server.trust.TrustAgentWrapper$2: void handleMessage(android.os.Message)>",
                "<com.android.server.net.NetworkPolicyManagerService: void updateRulesForAppIdleParoleUL()>",
                "<com.android.server.am.ActivityManagerShellCommand: int runStartActivity(java.io.PrintWriter)>",
                "<com.android.server.appop.AppOpsService$2: void onReceive(android.content.Context,android.content.Intent)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseBaseApkTag(java.lang.String,android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int)>",
                "<android.content.pm.parsing.ParsingPackageImpl: android.content.pm.parsing.ParsingPackageImpl addProperty(android.content.pm.PackageManager$Property)>",
                "<com.android.server.pm.PackageManagerService: com.android.server.pm.PackageManagerService$PrepareResult preparePackageLI(com.android.server.pm.PackageManagerService$InstallArgs,com.android.server.pm.PackageManagerService$PackageInstalledInfo)>",
                "<android.content.pm.parsing.ParsingPackageImpl: android.content.pm.parsing.ParsingPackageImpl addActivity(android.content.pm.parsing.component.ParsedActivity)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseProfileable(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.component.ParsedProcessUtils: android.content.pm.parsing.result.ParseResult parseDenyPermission(java.util.Set,android.content.res.Resources,android.content.res.XmlResourceParser,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseRestrictUpdateHash(int,android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseKeySets(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.component.ParsedProviderUtils: android.content.pm.parsing.result.ParseResult parseGrantUriPermission(android.content.pm.parsing.component.ParsedProvider,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseUsesPermission(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseKeySets(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseUsesSdk(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseUsesPermission(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.component.ParsedIntentInfoUtils: android.content.pm.parsing.result.ParseResult parseData(android.content.pm.parsing.component.ParsedIntentInfo,android.content.res.Resources,android.content.res.XmlResourceParser,boolean,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.IntentFilter: void addDataType(java.lang.String)>",
                "<android.content.IntentFilter: void processMimeType(java.lang.String,java.util.function.BiConsumer)>",
                "<android.content.pm.parsing.component.ParsedProviderUtils: android.content.pm.parsing.result.ParseResult parseGrantUriPermission(android.content.pm.parsing.component.ParsedProvider,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.ParsingPackageImpl: android.content.pm.parsing.ParsingPackageImpl setMetaData(android.os.Bundle)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseRestrictUpdateHash(int,android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.component.ParsedProviderUtils: android.content.pm.parsing.result.ParseResult parseGrantUriPermission(android.content.pm.parsing.component.ParsedProvider,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.ParsingPackageImpl: android.content.pm.parsing.ParsingPackageImpl setMetaData(android.os.Bundle)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseUsesStaticLibrary(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.ParsingPackageImpl: android.content.pm.parsing.ParsingPackageImpl addUsesStaticLibraryCertDigests(java.lang.String[])>",
                "<java.lang.System: void arraycopy(java.lang.Object,int,java.lang.Object,int,int)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseBaseApplication(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseSplitApplication(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int,int)>",
                "<android.content.pm.parsing.ParsingPackageImpl: android.content.pm.parsing.ParsingPackageImpl setSigningDetails(android.content.pm.PackageParser$SigningDetails)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseBaseApk(android.content.pm.parsing.result.ParseInput,java.io.File,java.lang.String,android.content.pm.split.SplitAssetLoader,int)>",
                "<android.content.pm.parsing.component.ParsedServiceUtils: android.content.pm.parsing.result.ParseResult parseService(java.lang.String[],android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int,boolean,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseBaseApplication(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseBaseApkTags(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.TypedArray,android.content.res.Resources,android.content.res.XmlResourceParser,int)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parsePermission(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>",
                "<android.content.pm.parsing.component.ParsedProcessUtils: android.content.pm.parsing.result.ParseResult parseProcesses(java.lang.String[],android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int,android.content.pm.parsing.result.ParseInput)>"
        };
        String methodSig = sigs[0];
        Body body = Utils.getBodyOfMethod(methodSig);
        System.out.println(body);
        /*for(Unit u : body.getUnits()){
            if(u instanceof DefinitionStmt){
                System.out.println("+++"+u);
            }
            if(u instanceof AssignStmt){
                System.out.println("---"+u);
            }
        }*/

        //UnitGraph ug = new ExceptionalUnitGraph(body);
        /*UnitGraph ug = new CompleteUnitGraph(body);
        TestImpl test = new TestImpl(ug);
        Unit unit = ug.getHeads().get(0);
        while(true){
            System.out.println(unit);
            System.out.println(test.getFlowAfter(unit));
            System.out.println(test.getFlowBefore(unit));
            unit = body.getUnits().getSuccOf(unit);
            if(unit == null) break;
            Utils.pause();
        }*/
        /*CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        Graph.generatePathsFromBlock(cbg.getHeads().get(0));
        System.out.println(Graph.paths.size());
        System.out.println(Utils.hasDuplicatedItems(Graph.paths));*/
        /*List<Value> v1 = new ArrayList<>();
        List<Value> v2 = new ArrayList<>();
       for(Unit unit : body.getUnits()) {
           if(unit instanceof AssignStmt){
               AssignStmt as = (AssignStmt) unit;
               if(as.getUseBoxes().size() == 2 && as.getRightOp().toString().contains(".<")){
                   v1.add(as.getRightOp());
               }
               break;
           }
       }
       for(Unit unit : body.getUnits()){
           if(unit instanceof AssignStmt) {
               AssignStmt as = (AssignStmt) unit;
               if(!Utils.hasRightValueOfAssignStmt(as, v1).isEmpty()){
                   System.out.println(as);
               }
           }
       }*/
    }


    private static void test4() {
        SootClass cls = Scene.v().getSootClassUnsafe("android.content.pm.parsing.ParsingPackageUtils");
        for (SootField sf : cls.getFields()) {
            System.out.println("--" + sf.getDeclaration());
        }
    }

    public static void test5() throws IOException, InterruptedException {
        String framework_path = sourceCode_base_path+"frameworks";
        String packages_path = sourceCode_base_path+"packages";
        getJavaFiles(packages_path);
        //copyFile(new File("src/Log.java"), "Log_copy.java");
        //File f = new File("src/Log.java");
        //System.out.println(f.getParent());
        //createDir("/data/disk_16t_2/leiry/1/2/3");
    }
    public static void getJavaFiles(String file_path){
        //System.out.println(file_path);
        if(file_path == null) return;
        File file = new File(file_path);
        if (file.isFile()) {
            if (file.getName().endsWith(".java")) {
                String dest_path = file.getAbsolutePath().replace(sourceCode_base_path, javaCode_path);
                System.out.println(dest_path);
                copyFile(file, dest_path);
            }
        } else if (file.isDirectory()) {
            File[] files = file.listFiles();
            for (File f : files) {
                getJavaFiles(f.getAbsolutePath());
            }
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
    public static void javaFileToClassFile(String file_path){
        try{
            File file = new File(file_path);
            if(file.isFile()){
                if(!file_path.endsWith(".java")) return;
                String dest_dir_path = file.getParent().replace(javaCode_path, classCode_path);
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
    public static void test6(){
        List<String> data = Log.readData(AnalysisForParsingClass.analysis_data);
        Set<String> methods = new HashSet<>();
        for(int i= 0; i< data.size(); i++){
            if(data.get(i).equals("--- Tainted callee.")){
                int j = i;
                while(true){
                    j = j -1;
                    if(data.get(j).startsWith("+ Unit:")){
                        String method = data.get(j).split(".<")[1].split(">")[0];
                        //System.out.println(method);
                        methods.add(method);
                        //Utils.pause();
                        break;
                    }
                }
            }
        }
        for(String method : methods){
            System.out.println(method);
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
            //System.out.println("****: " + Utils.isRightValueOfAssignment(as, vv));
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

