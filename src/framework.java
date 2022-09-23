import soot.*;

import soot.jimple.*;
import soot.options.Options;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.scalar.Pair;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.io.IOException;
import java.util.*;

public class framework {
    public static final String path = "/data/disk_16t_2/leiry/framework.apk";
    public static final String path_test = "test_java";

    public static List<String> call_path = new ArrayList<>();
    public static List<List<String>> call_paths = new ArrayList<>();
    public static Map<String, List<String>> methodToParents = new HashMap<String, List<String>>();

    public static void main(String[] args) throws IOException, InterruptedException {
        sootInitial(path);
        Utils.initializeAbstractClassesInfo();
        test1();
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
    private static void test1() {
        Log.deleteData(Log.element_data);
        Log.deleteData(Log.method_data);
        Log.deleteData(Log.analysis_data);
        Log.deleteData(Log.methods);

        Log.generatePrinterWriter(Log.analysis_data);

        String[] skip_nms = {"\"android\""};
        String[] skip_mds = {"obtainAttributes", "skipCurrentTag", "append", "unknownTag", "contains", "equals"};
        String[] no_analysis_mds = {"max", "min", "create", "digit", "composeLongVersionCode"};
        String[] skip_cls = {"android.content.res.XmlResourceParser", "android.content.pm.parsing.result.ParseInput", "com.android.internal.util.AnnotationValidations", "android.util.Slog"};
        String[] no_analysis_cls = {"com.android.internal.util.CollectionUtils", "android.text.TextUtils", "com.android.internal.util.ArrayUtils"};
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
            String tainted_element = tainted_point.getElement();
            List<SootMethod> tainted_parents = tainted_point.getParents();
            if(tainted_parents==null){
                tainted_parents = new ArrayList<>();
            }
            /*Utils.printPartingLine("#", Log.analysis_pw);
            Log.analysis_pw.println("+ Current analyzed method: " + tainted_method);
            Log.analysis_pw.println("+ Entry value: " + tainted_point.getValue());*/
            Log.logData(Log.analysis_data, Utils.generatePartingLine("#"));
            Log.logData(Log.analysis_data, "+ Current analyzed method: " + tainted_method);
            Log.logData(Log.analysis_data, "+ Entry value: " + tainted_point.getValue());
            int flag_analyzed = 0;
            for(Tainted atp : analyzed_tainted_points){
                if(atp.getMethod().equals(tainted_method)) {
                    flag_analyzed = 1;
                    Log.logData(Log.analysis_data, "This method has been analysed.");
                    Set<Pair<String, Value>> e_ds = atp.getElementAndStructure();
                    tainted_point.setElementAndStructure(e_ds); // The same method has the same <element, structure>.
                    if(e_ds != null) {
                        for (Pair<String, Value> e_d : e_ds) {
                            String e = e_d.getO1();
                            Value d = e_d.getO2();
                            String associated_element = Analysis.getAssociatedElement(tainted_element, e); // This element is related to the tainted method and its parents.
                            Analysis.storeAssociatedElementAndCorrespondingDataStructure(tainted_method, tainted_parents, associated_element, d);
                        }
                    }
                    // If this method tainted other methods, store their information.
                    Set<Tainted> children = atp.getChildren();
                    tainted_point.setTaintedChildren(children); // The same method has the same children.
                    if(children != null) {
                        List<SootMethod> parents = Utils.deepCopy(tainted_point.getParents());
                        parents.add(tainted_method);
                        for (Tainted child : children) {
                            String element = child.getElement(); // This element only associate with the tainted method.
                            String associated_element = Analysis.getAssociatedElement(tainted_element, element); // This element associate with the tainted method and its parents.
                            Analysis.tainted_points.offer(new Tainted(child.getMethod(), child.getValue(), associated_element, parents));
                        }
                    }
                    break;
                }
            }
            if(flag_analyzed==1) continue;

            analyzed_tainted_points.add(tainted_point);
            Analysis.dataFlowAnalysisForMethod(tainted_point);

            //Utils.pause();
        }

        for(Map.Entry<String, Set<Value>> entry: Analysis.associatedElementToDataStructures.entrySet()){
            System.out.println(entry.getKey() + " => " + entry.getValue().toString());
            String s = entry.getKey() + " => ";
            for(Value v : entry.getValue()){
                if(v.toString().contains(".<")){
                    s += v.toString();
                } else {
                    s += v.getType().toString();
                }
            }
            Log.logData(Log.elements, "=");
            Log.logData(Log.elements, s);
        }
    }

    // print body
    // given class name and method name
    public static void test2() {
        String className = "android.content.IntentFilter$$ExternalSyntheticLambda0";
        String methodName = "accept";
        //String className = "android.content.pm.parsing.component.ParsedPermission";
        //String className = "android.content.pm.parsing.result.ParseResult";
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        System.out.println(cls.getMethods());
        //String methodName = "addIntent";
        List<Body> bodies = Utils.getBodyOfMethod(className, methodName);
        for (Body body : bodies) {
            //System.out.println(body);
            for(Unit u : body.getUnits()){
                InvokeExpr ie = Utils.getInvokeOfUnit(u);
                if(ie!=null){
                    System.out.println(ie.getMethod().retrieveActiveBody());
                }
            }
        }
    }

    // print body
    // given method signature
    private static void test3() {
        String[] sigs = {
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
        String methodSig = sigs[14];
        Body body = Utils.getBodyOfMethod(methodSig);
        /*CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        Graph.generatePathsFromBlock(cbg.getHeads().get(0));
        System.out.println(Graph.paths.size());*/
        Value base = null;
        SootMethod m1 = null;
        SootMethod m2 = null;
        for(Unit unit : body.getUnits()){
            /*if(unit instanceof IdentityStmt){
                System.out.println(unit);
                IdentityStmt is = (IdentityStmt) unit;
                String s = is.getRightOp().toString();
                if(s.contains("@parameter")) {
                    int index = s.indexOf("@parameter");
                    System.out.println(s.charAt(index + 10));
                }
            }*/
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                if(ie!=null&&ie.getMethod().getName().equals("isError")){
                    if(m1==null){
                        m1 = ie.getMethod();
                    } else {
                        m2 = ie.getMethod();
                    }
                }
            }
        }
        System.out.println(m1.equals(m2));
        //System.out.println(Analysis.findCreationOfClassObject(body, base));
    }


    private static void test4() {
        SootClass cls = Scene.v().getSootClassUnsafe("android.content.pm.parsing.ParsingPackageUtils");
        for (SootField sf : cls.getFields()) {
            System.out.println("--" + sf.getDeclaration());
        }
    }

    public static void test5() throws IOException, InterruptedException {
        //Log.logData(Tainted.method_data, "test2");
        /*Tainted.test.offer("a");
        Tainted.test.offer("b");
        while (!Tainted.test.isEmpty()) {
            System.out.println("size: " + Tainted.test.size());
            String first = Tainted.test.poll();
            System.out.println("first: " + first);
            System.out.println("size: " + Tainted.test.size());
            String s = first + "c";
            Tainted.test.offer(s);
            Thread.sleep(2000);
        }*/
        /*String data1 = "test1";
        Store.logData("test.txt", data1);
        String data2 = "test2";
        Store.logData("test.txt", data2);*/
        /*InvokeExpr i = null;
        System.out.println(Utility.getBaseOfInvokeExpr(i));
        AssignStmt as = null;
        System.out.println(Utility.isParameter(i, null));*/
        /*Map<String, List<String>> methodToDataStructures = new HashMap<String, List<String>>();
        List<String> ds = methodToDataStructures.get("a");
        if(ds == null) {
            ds = new ArrayList<>();
            ds.add("a");
            methodToDataStructures.put("a", ds);
        } else{
            ds.add("a");
        }
        System.out.println(methodToDataStructures.get("b"));*/
        /*String a = null;
        System.out.println(a.equals("b"));*/
        //System.out.println("parseintentfilter".contains("intentfilter"));
        // InterfaceInvokeExpr iii;
        //SootClass cls =((RefType) iii.getBase().getType()).getSootClass();
        //cls.getInterfaces();
        /*String s1 = "intent-filter";
        String s2 = "parseIntentFilter";
        System.out.println(Utility.areRelatedNames(s1, s2));*/
        /*List<String> p1 = new ArrayList<>();
        p1.add("b");
        p1.add("c");
        methodToParents.put("a", p1);
        List<String> p2 = new ArrayList<>();
        p2.add("d");
        p2.add("e");
        methodToParents.put("b", p2);
        List<String> p3 = new ArrayList<>();
        p3.add("f");
        methodToParents.put("c", p3);
        generateCallPaths("a", 0, 0);
        System.out.println("call paths: " + call_paths);
        System.out.println(call_path);*/
        //System.out.println(Utility.isNumeric("000"));
        //Utility.printSymbols("-");
        /*Pair<String, String> p1 = new Pair<>("a", "b");
        Pair<String, String> p2 = new Pair<>("a", "b");
        System.out.println(p1.equals(p2));
        Set<Pair<String, String>> p = new HashSet<>();
        p.add(p1);
        //p.add(p2);
        System.out.println(p.contains(p2));
        System.out.println(p.size());*/
        /*InvokeExpr i =null;
        System.out.println(i instanceof VirtualInvokeExpr);*/
        /*List<String> a = null;
        for(String b : a){
            System.out.println("q");
        }*/
        /*String a = "1";
        String b = "2";
        String s = "a + b";
        String s1 = "0 == 1";
        System.out.println(Utils.isExpress(s1));
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("js");
        se.put("a", a);
        se.put("b", b);
        boolean result;
        try{
            result = (boolean) se.eval(s1);
            System.out.println(result ? 1:0);
            //System.out.println(result.getClass().getName());
        } catch (ScriptException e) {
            throw new RuntimeException(e);
        }*/
        /*List<String> strings = new ArrayList<>();
        strings.add("123");
        strings.add("12");
        strings.add("1234");
        System.out.println(strings);
        Collections.sort(strings, new StringComparator());
        System.out.println(strings);*/
        //Log.deleteData(Tainted.element_data);
        //List<String> data = Log.readData(Tainted.element_data);
        //System.out.println(data);
        /*List<List<Integer>> l = new ArrayList<>();
        List<Integer> l11 = new ArrayList<>();
        l11.add(1);
        l11.add(3);
        l.add(l11);
        List<Integer> l22 = new ArrayList<>();
        l22.add(2);
        l22.add(3);
        l.add(l22);
        System.out.println(l);
        List<Integer> l33 = l.get(0);
        l.remove(0);
        System.out.println(l);
        System.out.println(l33);*/
        /*List<Integer> l =new ArrayList<>();
        l.add(0);
        l.add(1);
        l.add(2);
        while(!l.isEmpty()){
            System.out.println(l.get(0));
            l.remove(0);
        }
*/
    Set<String> test = new HashSet<>();
    test.add("c");
    test.add("d");
    test.add("b");
    test.add("c");
    test.add("a");
        System.out.println(test);
    }
    public static void test6(ElementInfo test){
        test.getCaseIdToElement().put("1","test");
        int case_num = test.getCaseNum();
        case_num = 1;
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

