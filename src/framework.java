import soot.*;

import soot.jimple.*;
import soot.options.Options;
import soot.toolkits.scalar.Pair;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.io.IOException;
import java.util.*;

import static java.lang.Thread.sleep;

public class framework {
    public static final String path = "/data/disk_16t_2/leiry/framework.apk";
    public static final String path_test = "test_java";

    public static List<String> call_path = new ArrayList<>();
    public static List<List<String>> call_paths = new ArrayList<>();
    public static Map<String, List<String>> methodToParents = new HashMap<String, List<String>>();

    public static void main(String[] args) throws IOException, InterruptedException {
        sootInitial(path);
        Utils.initializeAbstractClassesInfo();
        findEntries();
        //findSuspiciousDataStructures();
        /*ElementInfo test = new ElementInfo();
        test6(test);
        System.out.println(test.getCaseNum());
        System.out.println(test.getCaseIdToElement());*/
    }

    private static void sootInitial(String apkPath) {
        soot.G.reset();
        // android.jar包位置
        Options.v().set_force_android_jar("lib/android31.jar");
        // 处理java则为Options.src_prec_java，处理jar包则为src_prec_J
        Options.v().set_src_prec(Options.src_prec_apk);
        // 该处测试用于apk，可注释
        Options.v().set_process_multiple_dex(true);
        // 以下不用管
        Options.v().set_process_dir(Collections.singletonList(apkPath));
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().ignore_resolution_errors();
        Scene.v().loadNecessaryClasses();
    }

    private static void sootInitial_test(String apkPath) {
        soot.G.reset();
        // android.jar包位置
        Options.v().set_force_android_jar("lib/android31.jar");
        Options.v().set_src_prec(Options.src_prec_java);
        // 以下不用管
        Options.v().set_process_dir(Collections.singletonList(apkPath));
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().ignore_resolution_errors();
        Scene.v().loadNecessaryClasses();
    }

    // analyse test.javad
    private static void test() {
        sootInitial_test(path_test);
        //SootClass cls =Scene.v().getSootClassUnsafe("test");
        /*for(SootMethod sm : cls.getMethods()){
            *//*for(Unit unit: sm.retrieveActiveBody().getUnits()){
                if(unit instanceof InvokeStmt){
                    InvokeExpr i = ((InvokeStmt) unit).getInvokeExpr();
                }
            }*//*
            System.out.println(sm.getDeclaringClass());
        }*/
        List<Body> bodies = Utils.getBodyOfMethod("test", "testSample");
        for (Body body : bodies) {
            System.out.println(body);
            //CompleteBlockGraph tug = new CompleteBlockGraph(body);
            //System.out.println(tug);
            for(Unit unit : body.getUnits()){
                /*if(unit instanceof AssignStmt){
                    AssignStmt as = (AssignStmt) unit;
                    System.out.println("---" + as);
                    *//*InvokeExpr i = Utility.getInvokeOfAssignStmt(as);
                    if(i!=null) {
                        if (i.getMethod().getName().equals("equals")) {
                            System.out.println(as);
                            System.out.println(i.getArgs().get(0));
                        }
                    }*//*
                }*/

                if(unit instanceof TableSwitchStmt){
                    TableSwitchStmt lss = (TableSwitchStmt) unit;
                    System.out.println(lss);
                }
                /*if (unit instanceof IfStmt){
                    IfStmt is = (IfStmt) unit;
                    System.out.println(is.getCondition());
                }
                if(unit instanceof GotoStmt){
                    GotoStmt gs = (GotoStmt) unit;
                    UnitBox ub = gs.getTargetBox();
                    System.out.println(ub.getUnit());
                    System.out.println(gs.getTarget());
                }*/
            }
        }
    }


    // find the methods related to the entry point
    private static void findSuspiciousDataStructures() throws InterruptedException {
        Log.deleteData(Log.element_data);
        Log.deleteData(Log.method_data);
        Log.deleteData(Log.analysis_data);
        Log.deleteData(Log.suspicious_structures);


        String[] skip_nms = {"\"android\"", "\"array\"", "\"singleInstancePerTask\""};
        String[] skip_mds = {"append", "obtainAttributes", "skipCurrentTag", "unknownTag"};
        String[] no_analysis_mds = {"max", "min", "create", "digit", "composeLongVersionCode", "computeMinSdkVersion", "computeTargetSdkVersion"};
        String[] skip_cls = {"android.content.res.XmlResourceParser", "android.content.pm.parsing.result.ParseInput", "com.android.internal.util.AnnotationValidations", "android.util.Slog"};
        String[] no_analysis_cls = {"com.android.internal.util.CollectionUtils", "android.text.TextUtils", "com.android.internal.util.ArrayUtils", "android.content.pm.parsing.FrameworkParsingPackageUtils"};
        SkipInfo.skip_names.addAll(new ArrayList<>(Arrays.asList(skip_nms)));
        SkipInfo.skip_methods.addAll(new ArrayList<>(Arrays.asList(skip_mds)));
        SkipInfo.no_analyzed_methods.addAll(new ArrayList<>(Arrays.asList(no_analysis_mds)));
        SkipInfo.skip_classes.addAll(new ArrayList<>(Arrays.asList(skip_cls)));
        SkipInfo.no_analyzed_classes.addAll(new ArrayList<>(Arrays.asList(no_analysis_cls)));

        List<Tainted> analyzed_tainted_points = new ArrayList<>();

        Analysis.findEntryPoints();

        while (!Analysis.tainted_points.isEmpty()) {
            Tainted tainted_point = Analysis.tainted_points.poll();
            SootMethod tainted_method = tainted_point.getMethod();
            String tainted_element = tainted_point.getOuterElement();

            int flag_analyzed = 0;
            for(Tainted atp : analyzed_tainted_points){
                if(atp.getMethod().equals(tainted_method)) {
                    flag_analyzed = 1; // This method has been analyzed.
                    List<Pair<String, String>> e_ds = atp.getInnerElementAndStructure();
                    tainted_point.setInnerElementAndStructure(e_ds); // The same method has the same <element, structure>.
                    if(e_ds != null) {
                        for (Pair<String, String> e_d : e_ds) {
                            String e = e_d.getO1();
                            String d = e_d.getO2();
                            String associated_element = Analysis.getAssociatedElement(tainted_element, e); // This element is related to the tainted method and its parents.
                            Analysis.storeAssociatedElementAndCorrespondingDataStructure(associated_element, d);
                        }
                    }
                    // If this method tainted other methods, store their information.
                    Set<Tainted> children = atp.getChildren();
                    tainted_point.setTaintedChildren(children); // The same method has the same children.
                    if(children != null) {
                        List<Tainted> parents = Utils.deepCopy(tainted_point.getParents());
                        parents.add(tainted_point);
                        for (Tainted child : children) {
                            String element = child.getOuterElement(); // This element only associate with the tainted method.
                            String associated_element = Analysis.getAssociatedElement(tainted_element, element); // This element associate with the tainted method and its parents.
                            Analysis.tainted_points.offer(new Tainted(child.getMethod(), child.getTaintedValues(), associated_element, parents, child.getCallUnit()));
                        }
                    }
                    break;
                }
            }

            if(flag_analyzed==1) {
                analyzed_tainted_points.add(tainted_point);
                continue;
            }

            Log.logData(Log.analysis_data, Utils.generatePartingLine("#"));
            Log.logData(Log.analysis_data, "+ Analyzed method: " + tainted_method);
            Log.logData(Log.analysis_data, "+ Entry value: " + tainted_point.getTaintedValues());
            analyzed_tainted_points.add(tainted_point);
            Analysis.dataFlowAnalysisForMethod(tainted_point);

            //Utils.pause();
            //sleep(2000);
        }

        for(Map.Entry<String, Set<String>> entry: Analysis.associatedElementToDataStructures.entrySet()){
            String associated_element = entry.getKey();
            Log.logData(Log.element_data, Utils.generatePartingLine("="));
            Log.logData(Log.element_data, "+ associated element: " + associated_element);
            String out = entry.getKey()+",";
            for(String ds : entry.getValue()){
                Log.logData(Log.element_data, Utils.generatePartingLine("*"));
                Log.logData(Log.element_data, "+ data structure: " + ds);
                out += ds + ",";
                if(ds!=null && ds.contains(".<") && ds.contains("ParsingPackageImpl")) {
                    String type = ds.split(" ")[1];
                    if (type.contains("list") || type.contains("List") || type.contains("[]") || type.contains("Queue") || type.contains("Stack")) {
                        Log.logData(Log.suspicious_structures, ds);
                        for (Tainted point : analyzed_tainted_points) {
                            List<Pair<String, String>> e_ds = point.getInnerElementAndStructure();
                            for (Pair<String, String> e_d : e_ds) {
                                String element = Analysis.getAssociatedElement(point.getOuterElement(), e_d.getO1());
                                if (associated_element.equals(element) && ds.equals(e_d.getO2())) {
                                    Log.logData(Log.element_data, Utils.generatePartingLine("-"));
                                    Log.logData(Log.element_data, "+ call path:");
                                    for (Tainted parent : point.getParents()) {
                                        Log.logData(Log.element_data, "--- " + parent.getMethod().getSignature());
                                    }
                                    Log.logData(Log.element_data, "---" + point.getMethod().getSignature());
                                }
                            }
                        }
                    }
                }
            }
            System.out.println(out);
        }
    }

    private static List<String> findEntries(){
        // Data preprocess.
        List<String> suspicious_structures = Log.readData(Log.suspicious_structures);
        List<String> suspicious_fields = new ArrayList<>();
        for(String structure : suspicious_structures){
            String f = "<" + structure.split(".<")[1];
            if(!suspicious_fields.contains(f)) {
                suspicious_fields.add(f);
            }
        }
        //System.out.println(suspicious_fields.size());

        String className = "android.content.pm.parsing.ParsingPackageImpl"; // The class for storing the parsed package's settings.
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        // Get the public fields of the class.
        List<String> public_fields = new ArrayList<>();
        for(SootField f : cls.getFields()){
            if(f.isPublic()){
                public_fields.add(f.getSignature());
            }
        }
        // Find the entries for accessing the suspicious data structures.
        List<String> entries = new ArrayList<>();
        for(String f : suspicious_fields){
            if(public_fields.contains(f)){ // The public field can be accessed through the corresponding class object.
                entries.add(f);
            }
        }
        for(SootMethod method : cls.getMethods()){
            String method_name = method.getName();
            if(method_name.startsWith("get")) {
                Body body = method.retrieveActiveBody();
                Value return_value = null;
                for (Unit unit : body.getUnits()) {
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        String right_op = as.getRightOp().toString();
                        if (right_op.contains(".<")) {
                            String likely_field = "<" + right_op.split(".<")[1];
                            if (suspicious_fields.contains(likely_field)) {
                                System.out.println(likely_field);
                                return_value = as.getLeftOp();
                            } else if(return_value!=null && return_value.equals(as.getLeftOp())){ // This value has been redefined.
                                return_value = null;
                            }
                        } else if (return_value!=null && return_value.equals(as.getLeftOp())){ // This value has been redefined.
                            return_value = null;
                        }
                    } else if (unit instanceof ReturnStmt) {
                        ReturnStmt rs = (ReturnStmt) unit;
                        if (return_value != null && return_value.equals(rs.getOp())) {
                            entries.add(method.getSignature());
                            //System.out.println(method);
                        }
                    }
                }
            }
        }
        return entries;
    }

    // print body
    // given class name and method name
    public static void test2() {
        String className = "android.content.pm.parsing.ParsingPackageImpl";
        String className2 = "android.content.pm.FeatureGroupInfo";
        String methodName = "getActivities";
        String methodName2 = "addActivity";
        String methodName3 = "assignDerivedFields";
        String methodName4 = "writeToParcel";
        //String className = "android.content.pm.parsing.component.ParsedPermission";
        //String className = "android.content.pm.parsing.result.ParseResult";
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        for(SootField f: cls.getFields()){
            if(f.isPublic()){
                System.out.println(f);
            }
        }
        //System.out.println(cls.getMethods());
        //String methodName = "addIntent";
        List<Body> bodies = Utils.getBodyOfMethod(className, methodName);
        Value v1 = null;
        for (Body body : bodies) {
            System.out.println(body);
            for(Unit u : body.getUnits()){
                if(u instanceof AssignStmt){
                    AssignStmt as = (AssignStmt) u;
                    if(as.getRightOp().toString().contains(".<")){
                        v1 = as.getRightOp();
                        System.out.println(v1.getUseBoxes());
                        System.out.println(as.getLeftOp().getType());
                    }
                }
            }
        }
        List<Body> bodies2 = Utils.getBodyOfMethod(className, methodName2);
        Value v2 = null;
        for(Body body : bodies2){
            for(Unit u : body.getUnits()){
                if(u instanceof AssignStmt){
                    AssignStmt as = (AssignStmt) u;
                    if(as.getLeftOp().equals(v1)){
                        System.out.println("---" + as);
                    }
                    if(as.getLeftOp().toString().contains(".<")){
                        v2 = as.getLeftOp();
                    }
                }
            }
        }
        System.out.println(v1);
        System.out.println(v2);
        System.out.println(v1.equals(v2));
        /*List<Body> bodies3 = Utils.getBodyOfMethod(className, methodName3);
        for(Body b : bodies3){
            System.out.println(b);
        }
        List<Body> bodies4 = Utils.getBodyOfMethod(className2, methodName4);
        for(Body b : bodies4){
            System.out.println(b);
        }*/
    }

    // print body
    // given method signature
    private static void test3() {
        String[] sigs = {
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
        String methodSig = sigs[22];
        Body body = Utils.getBodyOfMethod(methodSig);
        /*CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        Graph.generatePathsFromBlock(cbg.getHeads().get(0));
        System.out.println(Graph.paths.size());
        System.out.println(Utils.hasDuplicatedItems(Graph.paths));*/
        List<Value> v1 = new ArrayList<>();
        //List<Value> v2 = new ArrayList<>();
        List<Pair<String, SootMethod>> test = new ArrayList<>();
        Pair<String ,SootMethod> p = null;
       for(Unit unit : body.getUnits()) {
           if(unit instanceof AssignStmt){
               AssignStmt as = (AssignStmt) unit;
               v1.add(as.getLeftOp());
               //v2.add(as.getLeftOp());
               System.out.println(v1.hashCode());
               //System.out.println(v2.hashCode());
               break;
           }
       }
        System.out.println(test);
        System.out.println(test.contains(p));
    }


    private static void test4() {
        SootClass cls = Scene.v().getSootClassUnsafe("android.content.pm.parsing.ParsingPackageUtils");
        for (SootField sf : cls.getFields()) {
            System.out.println("--" + sf.getDeclaration());
        }
    }

    public static void test5() throws IOException, InterruptedException {
        String s = "r0.<android.content.pm.parsing.ParsingPackageImpl: java.util.List instrumentations>";
        String[] ss = s.split(" ");
        System.out.println(ss[1]);
        for(String a : ss){
            System.out.println(a);
        }
    }
    public static void test6(){
        List<String> l1 = new ArrayList<>();
        l1.add("a");
        List<String> l2 = new ArrayList<>();
        l2.add("b");
        System.out.println(l1.equals(l2));
        System.out.println(l1.hashCode());
        System.out.println(l2.hashCode());
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

