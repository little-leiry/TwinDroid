import org.jetbrains.annotations.Nullable;
import soot.*;

import soot.jimple.*;
import soot.jimple.spark.ondemand.pautil.SootUtil;
import soot.options.Options;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.graph.TrapUnitGraph;
import soot.toolkits.scalar.Pair;

import java.io.IOException;
import java.util.*;

public class framework {
    public static final String path = "/data/disk_16t_2/leiry/framework.apk";
    public static final String path_test = "test_java";

    public static void main(String[] args) throws IOException, InterruptedException {
        //sootInitial(path);
        //Map<List<SootMethod>, String> callPathToType =new HashMap<List<SootMethod>, String>();
        test5();
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

    // analyse test.java
    private static void test() {
        sootInitial_test(path_test);
/*        SootClass cls =Scene.v().getSootClassUnsafe("test");
        for(SootMethod sm : cls.getMethods()){
            for(Unit unit: sm.retrieveActiveBody().getUnits()){
                if(unit instanceof InvokeStmt){
                    InvokeExpr i = ((InvokeStmt) unit).getInvokeExpr();
                }
            }
        }*/
        List<Body> bodies = Utility.getBodyOfMethod("test", "testSample");
        for (Body body : bodies) {
            System.out.println(body);
            //CompleteBlockGraph tug = new CompleteBlockGraph(body);
            //System.out.println(tug);
            /*for(Unit unit : body.getUnits()){
                if (unit instanceof IfStmt){
                    IfStmt is = (IfStmt) unit;
                    System.out.println(is.getCondition());
                }
                if(unit instanceof GotoStmt){
                    GotoStmt gs = (GotoStmt) unit;
                    UnitBox ub = gs.getTargetBox();
                    System.out.println(ub.getUnit());
                    System.out.println(gs.getTarget());
                }
            }*/
        }
    }


    // find the methods related to the entry point
    private static void test1() {
        List<String> skip_methods = new ArrayList<>();
        String[] names = {"obtainAttributes", "skipCurrentTag", "Max", "Min", "append"};
        for (String name : names) {
            skip_methods.add(name);
        }
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
    }

    // print body
    // given class name and method name
    public static void test2() {
        //String className = "android.content.pm.parsing.component.ParsedComponentUtils";
        //String methodName = "addMetaData";
        String className = "android.content.pm.parsing.ParsingPackageUtils";
        String methodName = "parseBaseApk";
        List<Body> bodies = Utility.getBodyOfMethod(className, methodName);
        for (Body body : bodies) {
            //CompleteBlockGraph tug = new CompleteBlockGraph(body);
            //System.out.println(tug);
            System.out.println("++++" + body);
        }
    }

    // print body
    // given method signature
    private static void test3() {
        String methodSig = "<android.content.pm.parsing.component.ParsedComponentUtils: android.content.pm.parsing.result.ParseResult addMetaData(android.content.pm.parsing.component.ParsedComponent,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,android.content.pm.parsing.result.ParseInput)>";
        SootMethod sm = Scene.v().getMethod(methodSig);
        //Integer index = 1;
        //System.out.println(Utility.transfer(sm, index));
        Body body = Utility.getBodyOfMethod(methodSig);
        //System.out.println(body);
        for(Unit unit : body.getUnits()){
            System.out.println(unit);
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
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                System.out.println(as.getUseBoxes());
                System.out.println(as.getDefBoxes());
            }
        }
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
        InvokeExpr i = null;
        System.out.println(Utility.getBaseOfInvokeExpr(i));
        AssignStmt as = null;
        System.out.println(Utility.isParameter(i, null));

    }
}

