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
        String[] skip_mds = {"obtainAttributes", "skipCurrentTag", "append", "unknownTag"};
        String[] no_analysis_mds = {"max", "min", "create"};
        String[] skip_cls = {"android.content.res.XmlResourceParser", "android.content.pm.parsing.result.ParseInput"};
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

            //System.out.println(Tainted.tainted_points.size());

            /*Log.analysis_pw.close();
            Log.generatePrinterWriter(Tainted.analysis_data);*/
            //Utils.pause();
        }

        for(Map.Entry<String, Set<Value>> entry: Analysis.associatedElementToDataStructures.entrySet()){
            System.out.println(entry.getKey() + " => " + entry.getValue().toString());
        }
    }

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
        String[] sigs = {
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
        //System.out.println(body);
        for(Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                if(as.getLeftOp().toString().contains(".<")){
                    System.out.println(as);
                }
            }
        }
        try {
            body.getThisLocal();
        } catch (Exception e){
            System.out.println("NULL");
        }
        //Map<Value, String> valueToLikelyElement = new HashMap<>();
        /*List<Value> values = new ArrayList<>();
        for(Unit u : body.getUnits()){
            *//*if(u instanceof IdentityStmt){
                Value v = ((IdentityStmt) u).getLeftOp();
                values.add(v);
            }
            if(u instanceof AssignStmt){
                AssignStmt as = (AssignStmt) u;
                if(Utils.isCopyOfValues(as, values)){
                    System.out.println(u);
                }*//*
                *//*InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                if(ie!=null && ie.getMethod().getName().equals("getResult")){
                    System.out.println(as.getUseBoxes());
                    break;
                }*//*
                //Tainted.storeValueAndCorrespondingLikelyElement(as, valueToLikelyElement);
            if(u instanceof IfStmt){
            IfStmt is = (IfStmt) u;
                System.out.println(u);
                System.out.println(is.getConditionBox());
                System.out.println(is.getTarget());
                System.out.println(is.getUseBoxes());
                System.out.println();
            }
        }*/
        /*Log.logBody(body);
        Value p = Utils.getParameter(body.getMethod(), 0);
        System.out.println(p);*/
        //System.out.println(body);
        //CompleteBlockGraph tug = new CompleteBlockGraph(body);
        //Log.logCBG(tug);
        /*for(Block b : tug.getBlocks()){
            tug.getExceptionalPredsOf(b);
        }*/
        /*System.out.println(tug.getHeads().size());
        Block start_block = null;
        for(Block b : tug.getBlocks()){
            for(Unit u : b){
                if(u instanceof LookupSwitchStmt){
                 start_block = b;
                 break;
                }
            }
            if(start_block!=null) break;
        }
        System.out.println(start_block.getIndexInMethod());
        Graph.generatePathsFromBlock(start_block);*/
        //List<Block> blocks  = tug.getHeads();
       // System.out.println(blocks.size());

        /*for(Block b : tug.getBlocks()){
            //System.out.println("---: " + b.getIndexInMethod());
            for(Unit u : b){
                //System.out.println(u);
                if(u instanceof LookupSwitchStmt){
                    //System.out.println(u);
                    System.out.println("--- " + b.getIndexInMethod());
                    System.out.println("--- " + b.getHead());
                    LookupSwitchStmt lss = (LookupSwitchStmt) u;
                    if(lss.getDefaultTarget() instanceof GotoStmt){
                        GotoStmt gs = (GotoStmt) lss.getDefaultTarget();
                        System.out.println(gs.getTarget());
                        if(gs.getTarget() instanceof AssignStmt){
                            AssignStmt as = (AssignStmt) gs.getTarget();
                            System.out.println(as.getLeftOp());
                        }
                    }
                    System.out.println(lss.getTargets());

                }
            }
            //Utils.pause();
        }*/
        /*for(List<Integer> call_path : Graph.call_paths){
            System.out.println(call_path);
        }*/
        /*Utils.printPartingLine("-");
        Collections.sort(Graph.call_paths, new ListComparator());
        for(List<Integer> call_path : Graph.call_paths){
            System.out.println(call_path);
        }*/
        //System.out.println(tug);
        /*List<Value> vs = new ArrayList<>();
        for(Unit unit:body.getUnits()){
            if(unit instanceof AssignStmt) {
                AssignStmt as = (AssignStmt) unit;
                InvokeExpr i = Utils.getInvokeOfAssignStmt(as);
                if(i!=null && i.getMethod().getName().equals("parseProvider")){
                    List<ValueBox> vbs = as.getUseBoxes();
                    System.out.println(vbs);
                    Collections.sort(vbs, new VBComparator());
                    System.out.println(vbs);
                    System.out.println(body.getUnits().getSuccOf(unit));
                }
            }
        }*/
        //System.out.println(body);
       // String methodSig = ;
        //String methodSig3 = ;
        //String methodSig = "";
        //SootMethod sm = Scene.v().getMethod(methodSig);
        //SootMethod sm2 = Scene.v().getMethod(methodSig2);
        //SootMethod sm3 = Scene.v().getMethod(methodSig3);
        /*List<SootMethod> parents = new ArrayList<>();
        parents.add(sm2);
        Tainted t = new Tainted(sm, null, "test1", parents);
        List<SootMethod> p = Utils.deepCopy(t.getParents());
        p.add(sm3);
        Tainted t2 = new Tainted(sm2, null, "test2", p);
        System.out.println(t.getParents());
        System.out.println(t2.getParents());*/
       /* Tainted t = new Tainted(sm, null, null, null);
        System.out.println(t.getParents());
        System.out.println(t.getElement());
        System.out.println(t.getStartUnit());*/
        //System.out.println(sm.getSubSignature());
        //Integer index = 1;
        //System.out.println(Utility.transfer(sm, index));

        //List<Unit> b = Utility.bodyToList(body);
        /*for(Unit u : b){
            System.out.println(u);
        }*/
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
       /* Map<String, String> caseIdToElement = new HashMap<String, String>();
        Map<String, Unit> elementToUnit = new HashMap<String, Unit>();
        Map<String, SootMethod> elementToMethod = new HashMap<String, SootMethod>();
        Map<Value, String> likely_elements = new HashMap<Value, String>();
        Map<Value, String> numericValueToConcreteValue = new HashMap<Value, String>();
        int flag = 0;
        int count = 0;
        int case_num = 0;
        String element = "NULL";
        Value case_value = null;
        List<Unit> units = Utils.bodyToList(body);
        for(Unit unit : body.getUnits()) {
            if (unit instanceof AssignStmt) {
                AssignStmt as = (AssignStmt) unit;
                constructNumericValueToConcreteValue(as, numericValueToConcreteValue);
                createOrUpdateValueToLikelyElement(as, likely_elements);
            }
            int flag_element_cases = 0;
            // switch(element): case(XXX)=>parseXXX(parser)
            // LookupSwitchStmt($i1){case -12356 goto z0 = equals(XXX), b2 = 0}
            // LookupSwitchStmt(b2){case 0 goto $r6 = parseXXX(parser)}
            if (unit instanceof LookupSwitchStmt) {
                LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                if (case_value != null && lss.getUseBoxes().get(0).getValue().equals(case_value)) { // This LookupSwitchStmt is corresponding to the element's LookupSwitchStmt.
                    flag_element_cases = 1;
                }
                //System.out.println(lss.getUseBoxes());
                //System.out.println(lss.getTargets());
                for (int num = 0; num < lss.getTargetCount(); num++) {
                    Unit u = lss.getTarget(num);
                    if(u instanceof GotoStmt){
                        GotoStmt gs = (GotoStmt) u;
                        u = gs.getTarget();
                    }
                    InvokeExpr invoke = Utils.getInvokeOfUnit(u);
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
                                Utils.generatePartingLine("-");
                                elementToMethod.put(e, invoke.getMethod());
                                elementToUnit.put(e, u);
                                System.out.println(u);
                                System.out.println(e + " => " + invoke.getMethod().getName());
                            } else {
                                Utils.generatePartingLine("!");
                                System.out.println("Special element cases. The target unit does not contain an InvokeExpr:");
                                System.out.println(e + " => " + u);
                                System.out.println(units.indexOf(u));
                                Utils.generatePartingLine("!");
                            }
                        }
                    }
                }
            }

            if (unit instanceof AssignStmt) {
                AssignStmt as = (AssignStmt) unit;
                InvokeExpr i = Utils.getInvokeOfAssignStmt(as);
                if (i != null) {
                    if (i.getMethod().getName().equals("equals")) {
                        System.out.println(as);
                        if (i.getArg(0) instanceof StringConstant) {
                            element = i.getArg(0).toString();
                            //System.out.println("=====" + as);
                            flag = 1;
                        } else {
                            Value base = Utils.getBaseOfInvokeExpr(i);
                            //System.out.println(base);
                            if (base != null) {
                                if (likely_elements.containsKey(base)) {
                                    element = likely_elements.get(base);
                                    System.out.println(element);
                                    System.out.println("++++++" + as);
                                    flag = 1;
                                } else {
                                    System.out.println("Non-element-related equals: " + as);
                                }
                            }
                        }
                    }
                }
                //System.out.println(flag);
            }

            if (flag == 1 && case_num != 0) {
                count += 1;
                //System.out.println(count);
                if (count == 3) {
                    // Get the mapping relationship of two related LookupSwitchStmts
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        System.out.println(as.getLeftOp().getType());
                        if ("byte_int".contains(as.getLeftOp().getType().toString())) {
                            if (case_value == null) {
                                case_value = as.getLeftOp();
                            }
                        } else {
                            System.out.println("Special case: the third unit is not the case id transform.");
                            System.out.println(as);
                        }
                        String case_id = numericValueToConcreteValue.get(as.getLeftOp());
                        System.out.println(case_id + " => " + element);
                        caseIdToElement.put(case_id, element);
                    } else {
                        System.out.println("Special case: " + unit);
                        List<String> case_ids = Utils.intToList(case_num);
                        for (String case_id : case_ids) {
                            if (!caseIdToElement.containsKey(case_id)) {
                                System.out.println(case_id + " => " + element);
                                caseIdToElement.put(case_id, element);
                            }
                        }
                    }
                    element = "NULL";
                    flag = 0;
                    count = 0;
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
        Object result = null;
        try{
            result = se.eval(s1);
            System.out.println(result.getClass().getName());
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
        String s = "copy";
        System.out.println(s.contains("COPY"));

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

