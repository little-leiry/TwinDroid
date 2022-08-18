import org.jetbrains.annotations.Nullable;
import soot.*;

import soot.jimple.*;
import soot.jimple.spark.ondemand.pautil.SootUtil;
import soot.options.Options;

import java.util.*;

public class framework {
    public static final String path = "/data/disk_16t_2/leiry/framework.apk";
    public static final String path_test = "test";

    public static void main(String[] args) {
        sootInitial(path);
        Map<List<SootMethod>, String> callPathToType =new HashMap<List<SootMethod>, String>();
        Map<SootMethod, Value> entries = findEntryPoints();
        Iterator it = entries.keySet().iterator();
        while(it.hasNext()){
            SootMethod sm = (SootMethod) it.next();
            Value v = entries.get(sm);
            Body body = sm.retrieveActiveBody();
            for(Unit unit:body.getUnits()){
            }
        }
         //String className = "android.content.pm.parsing.component.ParsedComponentUtils";
         //String methodName = "addMetaData";
        String className = "android.content.pm.parsing.ParsingPackageUtils";
        String methodName = "parseUsesPermission";
        //String methodSig = "<java.lang.Math: int max(int,int)>";
        //Body body = Utility.getBodyOfMethod(methodSig);
        //System.out.println(body);
        List<Body> bodies = Utility.getBodyOfMethod(className, methodName);
        for(Body body:bodies){
            //System.out.println(body);
            for(Unit unit : body.getUnits()){
                InvokeExpr invoke = Utility.getCallee(unit);
                if(invoke != null){
                    if(invoke instanceof StaticInvokeExpr){
                        StaticInvokeExpr si = (StaticInvokeExpr) invoke;
                        //System.out.println(unit);
                        if(unit instanceof AssignStmt){
                            AssignStmt as = (AssignStmt) unit;
                            Value a = as.getLeftOp();
                            //System.out.println(a.getType().toString());
                        }
                    }
                }
            }
            for(Unit unit:body.getUnits()){
                InvokeExpr invoke = Utility.getCallee(unit);
                if(invoke!=null){
                    String calleeName = Utility.getNameOfCallee(invoke);
                    //System.out.println(calleeName);
                    if(calleeName.equals("parseRequiredFeature")){
                        System.out.println("---" + unit);
                        AssignStmt as = (AssignStmt) unit;
                        //String calleeSig=Utility.getSignatureOfCallee(invoke);
                        //System.out.println(as.getUseAndDefBoxes());
                        for(ValueBox vb : as.getUseBoxes()){
                            Value v = vb.getValue();
                            System.out.println(v.equals(v));
                            //System.out.println();
                        }
                        //Body b = Utility.getBodyOfMethod(calleeSig);
                        //System.out.println(b);
                       // for(Unit u : b.getUnits()){
                            //System.out.println(u.getDefBoxes());
                        //}
                        break;
                    }
                }
            }
        }
/*        SootClass cls = Scene.v().getSootClassUnsafe("android.content.pm.parsing.component.ParsedComponent");
        for(SootField sf : cls.getFields()){
            System.out.println(sf.getDeclaration());
        }*/
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

    private static void test(){
        List<Body> bodies = Utility.getBodyOfMethod("test", "testSample");
        for(Body body : bodies){
            System.out.println(body);
        }
    }

    private static Map<SootMethod, Value> findEntryPoints(){
        Map<SootMethod, Value> entries = new HashMap<SootMethod,Value>();
        String className = "android.content.pm.parsing.ParsingPackageUtils"; // the class for parsing an apk
        List<SootMethod> methods = Utility.getMethodsOfClass(className);
        for(SootMethod sm : methods){
            if(sm.isConcrete()){
                Body body = sm.retrieveActiveBody();
                for(Unit unit:body.getUnits()) {
                    InvokeExpr callee = Utility.getCallee(unit);
                    if (callee != null) {
                        // find the entry point
                        String calleeName = callee.getMethod().getName();
                        if (calleeName.equals("openXmlResourceParser")) {
                            //System.out.println(callee.getMethod().getSignature());
                            for (Value v : callee.getArgs()) {
                                if (v instanceof StringConstant) {
                                    String parameterName = v.toString();
                                    if (parameterName.equals("\"AndroidManifest.xml\"")) {
                                        //System.out.println(cls);
                                        //System.out.println(sm);
                                        //System.out.println(unit);
                                        //System.out.println("\n");
                                        //AssignStmt as = (AssignStmt) unit;
                                        //System.out.println(as);
                                        //InvokeExpr invoke = as.getInvokeExpr();
                                        //VirtualInvokeExpr vi = (VirtualInvokeExpr) invoke;
                                        //System.out.println("===" + vi.getBase());
                                        //Value entry = as.getLeftOp();
                                        //for(ValueBox vb : as.getUseBoxes()){
                                            //System.out.println(vb.getValue());
                                        //}
                                        //entries.put(sm, entry);
                                        //System.out.println("----"+entry);
                                        //System.out.println(body);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return entries;
    }

}
