import com.sun.org.apache.xpath.internal.operations.Bool;
import soot.*;
import soot.jimple.*;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class Tainted {
    // The tainted_methods needed to be analysed.
    // Use queue to do BFS.
    public static Queue<Pair<SootMethod, Value>> tainted_methods = new LinkedList<Pair<SootMethod, Value>>();
    public static Queue<String> test = new LinkedList<String>();
    // The parent method of some methods.
    // In order to construct call path of these methods.
    public static Map<String, List<SootMethod>> parentOfMethods = new HashMap<String, List<SootMethod>>();

    public Tainted(){}

    // ParseResult<ParsedPermission> result = ParsedPermissionUtils.parsePermission(
    //          pkg, res, parser, sUseRoundIcon, input);
    public static Boolean isTaintedByEntryPoint(AssignStmt as, Value entry){
        if (as.containsInvokeExpr()) {
            Value left = as.getLeftOp();
            InvokeExpr i = as.getInvokeExpr();
            if (Utility.isParameter(i, entry) != -1) {
                if (left.getType().toString().equals("android.content.pm.parsing.result.ParseResult")){
                    return true;
                }
            }
        }
        return false;
    }

/*    public static Boolean containTaintedValue(Unit unit, Value tainted_value){
        //parameter of the Invoke statement
        if(unit instanceof InvokeStmt){
            InvokeExpr i = (InvokeExpr) unit;
            return Utility.isParameter(i, tainted_value)!=-1;
        }
        //used value of the assignment statement
        if(unit instanceof AssignStmt){
            AssignStmt as = (AssignStmt) unit;
            return Utility.containValue(as, tainted_value);
        }
        return false;
    }*/

    public static void findEntryPoints() {
        //Map<SootMethod, Value> entries = new HashMap<SootMethod,Value>();
        String className = "android.content.pm.parsing.ParsingPackageUtils"; // the class for parsing an apk
        List<SootMethod> methods = Utility.getMethodsOfClass(className);
        for (SootMethod sm : methods) {
            if (sm.isConcrete()) {
                Body body = sm.retrieveActiveBody();
                for (Unit unit : body.getUnits()) {
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        InvokeExpr callee = Utility.getInvokeOfAssignStmt(as);
                        if (callee != null) {
                            // find the entry point
                            String calleeName = callee.getMethod().getName();
                            if (calleeName.equals("openXmlResourceParser")) {
                                for (Value v : callee.getArgs()) {
                                    if (v instanceof StringConstant) {
                                        String parameterName = v.toString();
                                        if (parameterName.equals("\"AndroidManifest.xml\"")) {
                                            System.out.println(as);
                                            Value entry = as.getLeftOp();
                                            tainted_methods.offer(new Pair<SootMethod, Value>(sm, entry));
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

    // skip_methods: important methods. If a statement contains this kind of methods, just skipping this statement.
    // no_analyzed_methods: these methods' functions have been known, no need to be analyzed.
    public static void DFAnalyseForMethod(SootMethod entry_method, Value entry_value, List<String> skip_methods, List<String> no_analyzed_methods){
        String element = "NULL";
        String data_structure = "NULL";
        Value tainted_value = null;
        int parsed_result_num = 0;
        Body body = entry_method.retrieveActiveBody();
        for(Unit unit:body.getUnits()){
            InvokeExpr i = null;
            Value base = null;
            SootMethod callee = null;
            String callee_name = "NULL";
            int need_analysis = 0;
            int assignStmt = 0;
            // A statement needs to be analysed only if it contains the tainted value.
            if(unit instanceof AssignStmt) {
                assignStmt = 1;
                AssignStmt as = (AssignStmt) unit;
                if (Utility.isUsedValueOfAssignment(as, entry_value) || Utility.isUsedValueOfAssignment(as, tainted_value)) {
                    need_analysis = 1;
                    i = Utility.getInvokeOfAssignStmt(as);
                }
            } else if (unit instanceof InvokeStmt) {
                i = ((InvokeStmt) unit).getInvokeExpr();
                if (Utility.isParameter(i, entry_value) != -1 || Utility.isParameter(i, tainted_value) != -1) {
                    need_analysis = 1;
                }
            }
            if (need_analysis == 0) continue;
            if(i!=null) {
                callee = i.getMethod();
                callee_name = callee.getName();
            }
            // result = XXX(parser)
            if (entry_value.getType().toString().equals("")){
                if(Utility.isParameter(i, entry_value) != -1){
                    if(! skip_methods.contains(callee_name)){
                        if (tainted_value !=null) {
                            data_structure = tainted_value.toString();
                        }
                        tainted_value = entry_value;
                        if (parsed_result_num > 0){
                            // log
                        }
                        parsed_result_num += 1;
                    }
                }
            }
            base = Utility.getBaseOfInvokeExpr(i);
            // Filter some statements that no need to be analyzed.
            if(base!=null){
                String base_type = base.getType().toString();
                if (base_type.equals("")){ // parser.XXX
                    continue;
                } else if (base_type.equals("android.content.pm.parsing.result.ParseInput")){ // input.xxx(tainted_value)
                    continue;
                } else if(base_type.equals("android.content.pm.parsing.result.ParseResult")) {
                    if (!callee_name.equals("getResult")) continue; // ! result.getResult()
                } else if(base.equals(tainted_value)){
                    if(!callee_name.startsWith("to")) continue; // ! tainted_value.toBundle()
                } else{
                    if(callee_name.equals("add") || callee_name.equals("put")){ // xxx.add(tainted_value)
                        data_structure = base_type;
                        // log
                        continue;
                    }
                }
            }
            // If the tainted value is passed in the callee, this callee is tainted.
            Integer parameter_index = Utility.isParameter(i, tainted_value);
            if(parameter_index!=-1){
                if(skip_methods.contains(callee_name)) continue;
                if(callee_name.startsWith("is")) continue;
                if(! no_analyzed_methods.contains(callee_name)){
                    Value parameter = Utility.transfer(callee, parameter_index);
                    tainted_methods.offer(new Pair<SootMethod, Value> (callee, parameter));
                    String parent_sig = entry_method.getSignature();
                    List<SootMethod> sms = parentOfMethods.get(parent_sig);
                    if(sms==null){ // This key is not exist.
                        sms = new ArrayList<>();
                        sms.add(callee);
                        parentOfMethods.put(parent_sig, sms);
                    }else{
                        sms.add(callee);
                    }
                }
            }
            // Pass the tainted value.
            if(assignStmt == 1){
                tainted_value = ((AssignStmt) unit).getLeftOp();
            }
        }
    }
}
