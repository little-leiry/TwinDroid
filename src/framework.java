import org.jetbrains.annotations.Nullable;
import soot.*;

import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.StringConstant;
import soot.options.Options;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class framework {
    public static final String path = "/data/disk_16t_2/leiry/framework.apk";

    public static void main(String[] args) {

        sootInitial(path);
        String className = "android.content.pm.parsing.ParsingPackageUtils"; // the class for parsing an apk
        List<SootMethod> methods = Utility.getMethodsOfClass(className);
        for(SootMethod sm : methods){
            if(sm.isConcrete()){
                Body body = sm.retrieveActiveBody();
                for(Unit unit:body.getUnits()){
                    if(unit instanceof AssignStmt){
                        AssignStmt as = (AssignStmt) unit;
                        if(as.containsInvokeExpr()){
                            InvokeExpr invoke = as.getInvokeExpr();
                            String calleeName = invoke.getMethod().getName();
                            if(calleeName.equals("openXmlResourceParser")){
                                //System.out.println(as);
                                for(Value v : invoke.getArgs()){
                                    //System.out.println(v);
                                    //System.out.println(v.getClass());
                                    if(v instanceof StringConstant){
                                        String parameterName = v.toString();
                                        //System.out.println("---" + parameterName);
                                        if(parameterName.equals("\"AndroidManifest.xml\"")){
                                            Value entry = as.getLeftOp();
                                            //System.out.println(entry);
                                            //System.out.println(as);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
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


}
