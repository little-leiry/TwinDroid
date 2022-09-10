import soot.*;

import soot.jimple.*;
import soot.options.Options;

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
        //Utility.initializeAbstractClassesInfo();
        //Map<List<SootMethod>, String> callPathToType =new HashMap<List<SootMethod>, String>();
        test3();
        //test1();


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
    /*private static void test1() {
        String[] skip_mds = {"obtainAttributes", "skipCurrentTag", "append"};
        String[] no_analysis_mds = {"max", "min", "create"};
        String[] skip_cls = {"android.content.res.XmlResourceParser", "android.content.pm.parsing.result.ParseInput"};
        String[] no_analysis_cls = {"CollectionUtils", "TextUtils"};
        List<String> skip_methods = Utility.stringsToList(skip_mds);
        List<String> no_analysis_methods = Utility.stringsToList(no_analysis_mds);
        List<String> skip_classes = Utility.stringsToList(skip_cls);
        List<String> no_analysis_classes = Utility.stringsToList(no_analysis_cls);

        List<SootMethod> analysed_methods = new ArrayList<>();
        Tainted.findEntryPoints();

        while (!Tainted.tainted_methods.isEmpty()) {
            Pair<SootMethod, Value> first = Tainted.tainted_methods.poll();
            SootMethod tainted_method = first.getO1();
            System.out.println("=========================================================");
            System.out.println("method: " + tainted_method);
            if (analysed_methods.contains(tainted_method)){
                System.out.println("This method is analysed.");
                continue;
            }
            analysed_methods.add(tainted_method);
            Value tainted_value = first.getO2();
            System.out.println("value: " + tainted_value);
            //Tainted.findTaintedMethods(tainted_method, tainted_value, skip_methods);
        }
    }*/

    // print body
    // given class name and method name
    public static void test2() {
        String className = "android.content.res.XmlBlock$Parser";
        String methodName = "getName";
        //String className = "android.content.pm.parsing.component.ParsedPermission";
        //String className = "android.content.pm.parsing.result.ParseResult";
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        System.out.println(cls.getMethods());
        //String methodName = "addIntent";
        List<Body> bodies = Utils.getBodyOfMethod(className, methodName);
        for (Body body : bodies) {
            System.out.println(body);
            //CompleteBlockGraph tug = new CompleteBlockGraph(body);
            //System.out.println(tug);
           /* for(Unit unit : body.getUnits()){
                if(unit instanceof AssignStmt){
                    AssignStmt as = (AssignStmt) unit;
                    System.out.println(as.getDefBoxes());
                }
            }*/
        }
    }

    // print body
    // given method signature
    private static void test3() {
        String methodSig = "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseBaseAppChildTag(android.content.pm.parsing.result.ParseInput,java.lang.String,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int)>";
        String methodSig2 = "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseBaseApkTag(java.lang.String,android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int)>";
        String methodSig3 = "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parsePermission(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>";
        //String methodSig = "<android.content.pm.parsing.component.ParsedProcessUtils: android.content.pm.parsing.result.ParseResult parseProcesses(java.lang.String[],android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int,android.content.pm.parsing.result.ParseInput)>";
        SootMethod sm = Scene.v().getMethod(methodSig);
        SootMethod sm2 = Scene.v().getMethod(methodSig2);
        SootMethod sm3 = Scene.v().getMethod(methodSig3);
        List<SootMethod> parents = new ArrayList<>();
        parents.add(sm2);
        Tainted t = new Tainted(sm, null, "test1", parents);
        List<SootMethod> p = Utils.deepCopy(t.getParents());
        p.add(sm3);
        Tainted t2 = new Tainted(sm2, null, "test2", p);
        System.out.println(t.getParents());
        System.out.println(t2.getParents());
        //System.out.println(sm.getSubSignature());
        //Integer index = 1;
        //System.out.println(Utility.transfer(sm, index));
        //Body body = Utility.getBodyOfMethod(methodSig);
        //List<Unit> b = Utility.bodyToList(body);
        /*for(Unit u : b){
            System.out.println(u);
        }*/
       /* CompleteBlockGraph tug = new CompleteBlockGraph(body);
        System.out.println(tug);*/
        /*for(Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                System.out.println("==================: " +as);
                System.out.println(as.getUseBoxes());
                if(!as.containsInvokeExpr()){
                    if(as.getUseBoxes().size()==2){
                        if(as.getUseBoxes().get(0).toString().contains(".<")) continue;
                        System.out.println("------------------: " + as);
                    }
                }
            }
            if(unit instanceof IdentityStmt){
                IdentityStmt is = (IdentityStmt) unit;
                System.out.println("++++++++++++++++++++: " + is);
                System.out.println(is.getRightOp());
            }
            InvokeExpr i = Utility.getInvokeOfUnit(unit);
            if(i!=null){
                if(i instanceof InterfaceInvokeExpr){
                    InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) i;
                    SootMethod s = ifi.getMethod();
                    //System.out.println(ifi);
                    SootClass cls =((RefType) ifi.getBase().getType()).getSootClass();
                    //System.out.println("----: " + cls);
                    //System.out.println(s);
                    if(s.getName().equals("addPermission")){
                        Utility.printSymbols("-");
                        Body b = Utility.getImplementedMethodOfAbstractMethod(ifi).retrieveActiveBody();
                        System.out.println(b);
                        Utility.printSymbols("-");
                    }
                }
            }
        }*/
        //System.out.println(body);
        /*Map<String, String> caseIdToElement = new HashMap<String, String>();
        Map<String, Unit> elementToUnit = new HashMap<String, Unit>();
        Map<String, SootMethod> elementToMethod = new HashMap<String, SootMethod>();
        Map<Value, String> likely_elements = new HashMap<Value, String>();
        int flag = 0;
        int count = 0;
        int case_num = 0;
        String element = "NULL";
        Value case_value = null;
        for(Unit unit : b){
            int flag_element_cases = 0;
            // switch(element): case(XXX)=>parseXXX(parser)
            // LookupSwitchStmt($i1){case -12356 goto z0 = equals(XXX), b2 = 0}
            // LookupSwitchStmt(b2){case 0 goto $r6 = parseXXX(parser)}
            if(unit instanceof LookupSwitchStmt){
                LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                if (case_value != null && lss.getUseBoxes().get(0).getValue().equals(case_value)) { // This LookupSwitchStmt is corresponding to the element's LookupSwitchStmt.
                    flag_element_cases = 1;
                }
                //System.out.println(lss.getUseBoxes());
                //System.out.println(lss.getTargets());
                for (int num = 0; num < lss.getTargetCount(); num++) {
                    Unit u = lss.getTarget(num);
                    InvokeExpr invoke = Utility.getInvokeOfUnit(u);
                    if (invoke != null) {
                        if (invoke.getMethod().getName().equals("equals")) { // This LookupSwitchStmt is related to elements.
                            case_num = lss.getTargetCount(); // The number of elements.
                            break;
                        }
                    }
                    if (flag_element_cases == 1) {
                        String case_id = ((Integer) lss.getLookupValue(num)).toString();
                        if (caseIdToElement.containsKey(case_id)) {
                            String e = caseIdToElement.get(case_id);
                            if (invoke != null) {
                                Utility.printSymbols("-");
                                elementToMethod.put(e, invoke.getMethod());
                                elementToUnit.put(e, u);
                                System.out.println(u);
                                System.out.println("index: " + b.indexOf(u));
                                System.out.println(e + " => " + invoke.getMethod().getName());
                            } else {
                                Utility.printSymbols("!");
                                System.out.println("Special element cases. The target unit does not contain an InvokeExpr:");
                                System.out.println(e + " => " + u);
                                int index  = b.indexOf(u);
                                System.out.println("Find the appropriate target unit ...");
                                while(true){
                                    Unit uu = b.get(index+1);
                                    InvokeExpr ii = Utility.getInvokeOfUnit(uu);
                                    if(ii != null){
                                        elementToUnit.put(e, uu);
                                        System.out.println(e + " => " + ii.getMethod().getName());
                                        break;
                                    }
                                    index+=1;
                                }
                                Utility.printSymbols("!");
                            }
                        }
                    }
                }
            }

            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                InvokeExpr i = Utility.getInvokeOfAssignStmt(as);
                if(as.getUseBoxes().get(0).getValue() instanceof StringConstant){
                    System.out.println(as);
                    Value element_value = as.getLeftOp();
                    element = as.getUseBoxes().get(0).getValue().toString();
                    likely_elements.put(element_value, element);
                    System.out.println(element_value + " => " + element);
                }
                if(i!=null){
                    if(i.getMethod().getName().equals("equals")){
                        //System.out.println(as);
                        if(i.getArg(0) instanceof StringConstant) {
                            element = i.getArg(0).toString();
                            //System.out.println("=====" + as);
                        } else {
                            Value base = Utility.getBaseOfInvokeExpr(i);
                            //System.out.println(base);
                            if (base != null){
                                if(likely_elements.containsKey(base)){
                                    element=likely_elements.get(base);
                                    System.out.println(element);
                                    System.out.println("++++++" + as);
                                } else {
                                    System.out.println("false");
                                }
                            }
                        }
                        flag = 1;
                    }
                    if(elementToMethod.containsValue(i.getMethod())){
                        Utility.printSymbols("%");
                        System.out.println(i.getMethod());
                        for (Map.Entry<String, SootMethod> entry : elementToMethod.entrySet()) {
                            if (i.getMethod().equals(entry.getValue())) {
                                System.out.println(entry.getKey());
                            }
                        }
                    }
                }
                //System.out.println(flag);
            }

            if(flag == 1 && case_num !=0){
                count += 1;
                //System.out.println(count);
                if(count == 3){
                    // Get the mapping relationship of two related LookupSwitchStmts
                    if (unit instanceof AssignStmt){
                        AssignStmt as = (AssignStmt) unit;
                        String case_id = as.getUseBoxes().get(0).getValue().toString();
                        if(case_value==null) {
                            case_value = as.getLeftOp();
                        }
                        System.out.println(case_id + " => " + element);
                        caseIdToElement.put(case_id, element);
                    } else {
                        System.out.println("Special case: " + unit);
                        List<String> case_ids = Utility.intToList(case_num);
                        for(String case_id : case_ids){
                            if(!caseIdToElement.containsKey(case_id)){
                                System.out.println(case_id + " => " + element);
                                caseIdToElement.put(case_id, element);
                            }
                        }
                    }
                    element = "NULL";
                    flag=0;
                    count=0;
                }
            }

            if(elementToUnit.containsValue(unit)){
                Utility.printSymbols("+");
                System.out.println(unit);
                System.out.println(b.indexOf(unit));
                for (Map.Entry<String, Unit> entry : elementToUnit.entrySet()) {
                    if (unit.equals(entry.getValue())) {
                        System.out.println(entry.getKey());
                    }
                }
            }
        }
        System.out.println(flag);
        System.out.println(count);
        System.out.println(element);*/
        /*for(Unit unit: body.getUnits()){
            System.out.println(unit);
            //System.out.println(unit instanceof IdentityStmt);
            if(unit instanceof IdentityStmt){
                IdentityStmt is = (IdentityStmt) unit;
                System.out.println(is.getRightOp().toString().contains("@parameter0:"));
            }
            for(ValueBox vb : unit.getUseBoxes()){
                System.out.println(vb.getValue().toString().contains("@parameter"));
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
        p.add(p2);
        System.out.println(p);
        System.out.println(p.size());*/
        /*InvokeExpr i =null;
        System.out.println(i instanceof VirtualInvokeExpr);*/
        List<String> a = null;
        for(String b : a){
            System.out.println("q");
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
}

