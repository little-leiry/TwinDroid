package analysis;

import comparator.VBComparator;
import graph.Graph;
import org.apache.commons.collections4.CollectionUtils;
import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.scalar.Pair;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.lang.reflect.Field;
import java.util.*;

import static java.lang.System.exit;
import static java.lang.System.out;

public class AnalysisForParsingClass2 extends Analysis {
    // The class for parsing an apk.
    public static final String parsing_class = "android.content.pm.parsing.ParsingPackageUtils";
    // The class for store the parsed package's settings.
    public static final String parsedPackage_settings_class = "android.content.pm.parsing.ParsingPackageImpl";


    // The base units needed to be analysed.
    // Each object consists of <base method, source variable set, associated element type>
    // Use queue to do BFS.
    public static Queue<BU> base_units = new LinkedList<BU>();

    // element name => data structures.
    public static Map<String, Set<String>> associatedElementTypeToDataStructures = new HashMap<String, Set<String>>();
    public static Map<String, Value> struFieldToSupportingObj = new HashMap<>();
    public static final String element_data = store_base_path + "logs/parsing/element_data.txt";
    public static final String method_data = store_base_path + "logs/parsing/method_data.txt";
    public static String analysis_data = store_base_path + "logs/parsing/analysis_data.txt";
    public static String target_settings = store_base_path + "logs/parsing/target_settings.txt";

    public static String package_settings = store_base_path + "logs/parsing/package_settings.txt";

    // Situation 1:
    // r9 = "application";
    // $z1 = virtualinvoke r9.<java.lang.String: boolean equals(java.lang.Object)>($r8);
    // if $z1 == 0 goto $r6 = specialinvoke r0.<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult
    // Situation 2:
    // $z0 = virtualinvoke $r1.<java.lang.String: boolean equals(java.lang.Object)>("compatible-screens");
    // if $z0 == 0 goto (branch);
    public static boolean isElementTypeRelated(AssignStmt as, Body body, Unit unit){
        if(as == null || body == null) return false;
        Unit next_unit = body.getUnits().getSuccOf(unit);
        Unit next_next_unit = next_unit == null? null: body.getUnits().getSuccOf(next_unit);

        Value right_op = as.getRightOp();
        Value left_op = as.getLeftOp(); // z0 or r1
        if(right_op instanceof StringConstant){ // r1 = "element_type";
            String likely_element = right_op.toString();
            if (likely_element.startsWith("\"/")) return false;
            if (likely_element.startsWith("\"android.permission")) return false;
            if (skip_names.contains(likely_element)) return false;
            if(next_unit instanceof AssignStmt){ // z0 = r1.equals(r2)
                AssignStmt next_as = (AssignStmt) next_unit;
                Value next_as_left_op = next_as.getLeftOp();
                InvokeExpr next_ie = Utils.getInvokeOfAssignStmt(next_as);
                Value next_base = Utils.getBaseOfInvokeExpr(next_ie);
                if(next_ie != null && next_ie.getMethod().getName().equals("equals") && left_op.equals(next_base)) { // r1.equals(r2)
                    if(next_next_unit instanceof IfStmt){ // if (z0 == 1) goto XXXX.
                        IfStmt next_next_is = (IfStmt) next_next_unit;
                        if(next_next_is.getUseBoxes().get(0).getValue().equals(next_as_left_op)){
                            return true;
                        }
                    }
                }
            }
        } else if (as.containsInvokeExpr()){
            InvokeExpr ie = as.getInvokeExpr();
            String method_name = ie.getMethod().getName();
            if (method_name.equals("equals")) {
                if (ie.getArg(0) instanceof StringConstant) { // z0 = parser.getName().equals(element_type)
                    String s = ie.getArg(0).toString();
                    if (s.startsWith("\"/")) return false;
                    if (s.startsWith("\"android.permission")) return false;
                    if (skip_names.contains(s)) return false;
                    if(next_unit instanceof IfStmt){
                        IfStmt next_is = (IfStmt) next_unit;
                        if(next_is.getUseBoxes().get(0).getValue().equals(left_op)){ //if(z0 == 1) goto XXXX
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    public static boolean isIdentifierRelatedForPairVariable(BU base_unit, Value pair_value, Set<Value> identifier_variables){
        if(base_unit == null || pair_value == null) return false;

        Value v1 = pair_value.getUseBoxes().get(0).getValue();
        Value v2 = pair_value.getUseBoxes().get(1).getValue();
        if(identifier_variables!=null && (identifier_variables.contains(v1) || identifier_variables.contains(v2)))
            return true;
        List<Value> vars = new ArrayList<>();
        vars.add(v1);
        vars.add(v2);
        for(Value v : vars) {
            if (Utils.isStringVariable(v)) {
                if (!base_unit.getParameters().containsKey(v)) {
                    Body body = base_unit.getBaseMethod().retrieveActiveBody();
                    Unit end_unit = null;
                    for (Unit u : body.getUnits()) {
                        if (u instanceof AssignStmt) {
                            AssignStmt as = (AssignStmt) u;
                            if (as.getRightOp().equals(pair_value)) {
                                end_unit = u;
                                break;
                            }
                        }
                    }
                    return isIdentifierVariable(base_unit.getBaseMethod().getName(), body, v1, end_unit);
                } else {
                    Pair<Pair<BU, Value>, Unit> belonging_bu_info = findBelongingBUOfVariable(base_unit, v);
                    BU belonging_bu = belonging_bu_info.getO1().getO1();
                    Value corresponding_var = belonging_bu_info.getO1().getO2();
                    Unit call_unit = belonging_bu_info.getO2();
                    if (belonging_bu != null) {
                        SootMethod belonging_sm = belonging_bu.getBaseMethod();
                        /*out.println("### belonging method: " + belonging_sm);
                        out.println("### corresponding var: " + corresponding_var);
                        out.println("### call unit: " + call_unit);
                        out.println("### " + isIdentifierVariable(belonging_sm.getName(), belonging_sm.retrieveActiveBody(), corresponding_var, call_unit));*/
                        return isIdentifierVariable(belonging_sm.getName(), belonging_sm.retrieveActiveBody(), corresponding_var, call_unit);
                    }
                }
            }
        }
        return false;
    }

    public static boolean isNoteworthyUnit(BU base_unit, Body body, Unit unit, List<Value> source_variables, Set<AssignStmt> source_defs){
        if(source_variables.isEmpty()) return false;

        // If there exists definition statements of source variables, we only care about these definition statements.
        if(source_defs!=null){
            if(unit instanceof AssignStmt){
                AssignStmt as =(AssignStmt) unit;
                // Noteworthy unit -- Definition of the source variables.
                if(source_defs.contains(as)){
                    return true;
                }
            }
            return false;
        }
        // For the situation that the source_defs is empty.
        if(unit instanceof AssignStmt){
            AssignStmt as =(AssignStmt) unit;
            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Noteworthy unit -- Related to element types.
            if (isElementTypeRelated(as, body, unit)) {
                if(confirmElementType(body, unit)) {
                    return true;
                }
            }
            // Noteworthy unit -- The source variable appears in the right of the Assignment statement.
            if(!hasRightVarsOfAssignStmt(as, base_unit, analysis_data, source_variables).isEmpty()) {
                // Filter some uninteresting types.
                if(Utils.hasCopyOfVars(as, source_variables)){
                    return false;
                }
                if (source_variables.contains(base)) {
                    if(base.getType().toString().endsWith("Parser")){
                        return false;
                    }
                    String method_name = ie.getMethod().getName();
                    if(canSkipForInflowBase(base, method_name)){
                        return false;
                    }
                }
                if (!hasParamsOfInvokeExpr(base_unit, ie, analysis_data, source_variables).isEmpty()) {
                    SootMethod method = ie.getMethod();
                    String method_name = method.getName();
                    int flag_array=0;
                    for(Value entry : source_variables){
                        if(entry.getType().toString().equals("android.content.res.TypedArray")){
                            flag_array = 1;
                            break;
                        }
                    }
                    if(canSkipForInflowParameter(base, method, method_name, flag_array)){
                        return false;
                    }
                }
                return true;
            }
        } else if (unit instanceof InvokeStmt) {
            InvokeExpr ie = ((InvokeStmt) unit).getInvokeExpr();
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- pass in the entry value as a parameter.
            if (!hasParamsOfInvokeExpr(base_unit, ie, analysis_data, source_variables).isEmpty()) {
                SootMethod method = ie.getMethod();
                String method_name = method.getName();
                int flag_array=0;
                for(Value entry : source_variables){
                    if(entry.getType().toString().equals("android.content.res.TypedArray")){
                        flag_array = 1;
                        break;
                    }
                }
                if(canSkipForInflowParameter(base, method, method_name, flag_array)){
                    return false;
                }
                return true;
            }
            // Noteworthy unit -- the source variable is the base of the method toArray.
            if(source_variables.contains(base)){
                String method_name = ie.getMethod().getName();
                if(method_name.equals("toArray")){
                    return true;
                }
            }
        }
        return false;
    }

    public static boolean isSpecialMethod(String method_name){
        String[]  sms = {"parseUsesPermission", "parseUsesSdk", "parseKeySets", "parseQueries", "parseUsesStaticLibrary"};
        List<String> special_methods = new ArrayList<>(Arrays.asList(sms));
        if(special_methods.contains(method_name)){
            return true;
        }
        return false;
    }

    // A target package setting should meet:
    // 1. ParsingPackageImpl class's field
    // 2. Duplication-type data structure
    // 3. Data structure's supporting object's type has > 1 attributes and involve the identifier.
    public static boolean isTargetPackageSetting(String ds){
        if(ds!=null && ds.contains("<") && ds.contains(parsedPackage_settings_class)) {
            if(ds.contains("unsuitable")){
                return false;
            }
            String type = ds.split(" ")[1];
            if ((type.endsWith("Map") || type.endsWith("SparseArray"))){ // For the type of Map
                if(ds.endsWith("value") && !ds.contains("key(identifier)")){
                    return true;
                }
            }
            if(type.endsWith("List") || type.endsWith("[]") || type.endsWith("Queue") || type.endsWith("Stack")) {
                return true;
            }
        }
        return false;
    }

    // For the situation that the passing variable is a parameter of a method.
    public static boolean isAttrOfPassingVar(String method_name){
        if(method_name.startsWith("get")){
            //System.out.println("=== " + ie);
            return true;
        }
        return false;
    }

    // For the situation that the passing variable is the base of a method.
    public static boolean isAttrOfPassingVar(Value base, String method_name){
        if(base != null){
            // $r6 = virtualinvoke r4.<android.content.pm.parsing.component.ParsedProvider: java.lang.String getAuthority()>()
            if(method_name.startsWith("get") && !method_name.equals("getResult")){
                return true;
            }
            // $r7 = virtualinvoke $r6.<java.lang.String: java.lang.String[] split(java.lang.String)>(";")
            if("split_values_keySet_entrySet".contains(method_name)){
                return true;
            }
        }
        return false;
    }

    // For the situation that the statement does not contain an invocation.
    public static boolean isAttrOfPassingVar(AssignStmt as){
        List<ValueBox> vbs = as.getUseBoxes();
        String right_op = as.getRightOp().toString();
        if (vbs.size() == 1){
            if(Utils.isCopyStmt(as)) { // r1 = r2
                return true;
            }
        }else if(vbs.size() == 2) {
            // $r6 = $r5.<android.content.pm.parsing.component.ParsedAttribution: java.lang.String tag>
            if(right_op.contains(".<")){
                return true;
            }
        } else if (vbs.size() == 3){
            // $r6 = $r7[i2]
            if(right_op.contains("[")){
                return true;
            }
        }
        return false;
    }

    public static boolean canSkipForInflowBase(Value base, String method_name){
        String base_type = base.getType().toString();
        String declaring_class = ((RefType) base.getType()).getSootClass().getName();

        if (base_type.endsWith("ParseResult")) {
            if (!method_name.equals("getResult")) { // result.getResult()
                return true;
            }
        }

        if(base_type.equals("java.util.Iterator")){
            if(method_name.equals("hasNext")){
                return true;
            }
        }
        if(base_type.equals("java.util.StringTokenizer")){
            if(method_name.equals("hasMoreElements")){
                return true;
            }
        }
        if(method_name.startsWith("remove") || method_name.startsWith("dump") || method_name.startsWith("count")){
            return true;
        }
        if(skip_classes.contains(declaring_class) || skip_methods.contains(method_name)){
            return true;
        }
        return false;
    }

    public static boolean canSkipForInflowParameter(Value base, SootMethod method, String method_name, int flag_array){
        String declaring_class;
        if (base != null) {
            declaring_class = ((RefType) base.getType()).getSootClass().getName();
        } else {
            declaring_class = method.getDeclaringClass().getName();
        }
        if (skip_methods.contains(method_name) || skip_classes.contains(declaring_class)) {
            return true;
        }
        if(flag_array==0 && method.getReturnType().toString().equals("boolean") && !method_name.equals("add")){
            return true;
        }
        if (method_name.startsWith("remove")) {
            return true;
        }
        return false;
    }

    // The element type associated with an AssignStmt and IfStmt.
    public static boolean confirmElementType(Body body, Unit unit){
        if(body == null || unit ==  null) return false;

        // Confirm.
        if(unit instanceof AssignStmt){
            AssignStmt as = (AssignStmt) unit;
            Value left_op = as.getLeftOp();
            Unit next_unit = body.getUnits().getSuccOf(unit);
            if(next_unit instanceof IfStmt){
                IfStmt is = (IfStmt) next_unit;
                if(is.getUseBoxes().get(0).getValue().equals(left_op)){
                    return true;
                }
            }
        }
        return false;
    }

    public static boolean needGenerateNewBaseUnit(int assignStmt, int flag_parser, String callee_name){
        if(assignStmt == 1){
            if(flag_parser == 1){
                return true;
            } else if (callee_name.startsWith("add") && !"add_addAll".contains(callee_name)){
                return true;
            } else if (callee_name.startsWith("set") && !callee_name.equals("set")){
                return true;
            } else {
                return false;
            }
        } else{
            return true;
        }
    }

    public static boolean needUpdateElementType(List<Block> blocks, List<Integer> block_ids, int block_ids_index, IfStmt is, Value element_type_boolean ){
        if (is == null || element_type_boolean == null) return false;

        Value boolean_express_variable = is.getUseBoxes().get(0).getValue();
        if(boolean_express_variable.equals(element_type_boolean)){
            String condition = is.getCondition().toString();
            //System.out.println("Condition: " + condition);
            Unit next_unit = blocks.get(block_ids.get(block_ids_index + 1)).getHead();
            //System.out.println("Next unit: " + next_unit);
            Unit target_unit = is.getTarget();
            //System.out.println("Target unit: " + target_unit);
            if(condition.contains("== 1") || condition.contains("!= 0")){ // r1.equal(element_type) is true;
                if(target_unit.equals(next_unit)) { // The recorded element type is associated with this path;
                    return false;
                }
                return true;
            } else if (condition.contains("== 0") || condition.contains("!= 1")){ // r1.equal(element_type) is false;
                if(target_unit.equals(next_unit)){ // The recorded element type is not associated with this path;
                    return true;
                }
                return false;
            }
        }
        return false;
    }

    public static void adjustVariableSetIfVariableRedefined(AssignStmt as, BU base_unit, String element_type, InvokeExpr ie, Value return_variable, List<Unit> passing_units,
                                                            List<Value> passing_variables, List<Value> source_variables, Set<Value> identifier_variable, Set<AssignStmt> source_defs,
                                                            Map<Value, Value> newVariableToCopy, Map<Value, String> passingMapVariableToInflowItem,
                                                            Map<Value, Value> passingStruVariableToSupportingObj, Map<Value, String> variableToField){
        Unit last_passing_unit = passing_units.isEmpty()?  null : passing_units.get(passing_units.size() - 1);
        Value redefined_value = hasRedefinedVariable(as, ie, source_variables, last_passing_unit, source_defs, variableToField);
        if (redefined_value != null) {
            source_variables.remove(redefined_value);
            Log.logData(analysis_data, "=");
            String msg = "+ Unit: " + as + "\n--- The source variable [ " + as.getLeftOp() + " ] is re-defined, remove it." +
                    "\n--- Updated the source variable set: " + source_variables;
            Log.logData(analysis_data, msg);
        } else {
            redefined_value = hasRedefinedVariable(as, ie, passing_variables, last_passing_unit, source_defs, variableToField);
            if (redefined_value!=null) {
                Log.logData(analysis_data, Utils.generatePartingLine("="));
                Log.logData(analysis_data, "+ Unit: " + as);
                Log.logData(analysis_data, "--- The passing variable [ " + as.getLeftOp() + " ] is re-defined.");
                // Save info.
                Log.logData(analysis_data, "+ Save information -- variable re-defined.");
                saveDataStructureAndRelatedInfo(base_unit, element_type, redefined_value, return_variable, identifier_variable,
                        passingMapVariableToInflowItem, passingStruVariableToSupportingObj, variableToField);
                // Update the passing variable set.
                removeVariable(redefined_value, passing_variables, newVariableToCopy);
                Log.logData(analysis_data, "--- Update the passing variable set: " + passing_variables);
            }
        }
        // For the situation that multiple definition statement corresponding to the same source variable.
        // The source variable may be removed due to value re-defining.
        // So we need add the source variable to the source variable set again.
        if(source_defs!=null && source_defs.contains(as)){
            if(!source_variables.contains(as.getLeftOp())){
                source_variables.add(as.getLeftOp());
                String msg = "+ Definition statement: " + as + "\n--- Updated the source variable: " + source_variables;
                Utils.logMsg(analysis_data, msg, "+");
            }
        }
    }

    public static void adjustVariableSetIfElementTypeUpdate(BU base_unit, String element_type, Value return_variable, Set<Value> identifier_variables, List<Unit> passing_units,
                                                            List<Value> passing_variables, Map<Value, String> passingMapVariableToInflowItem,
                                                            Map<Value, Value> passingStruVariableToSupportingObj, Map<Value, String> variableToField){
        if(element_type != null || !passing_variables.isEmpty()) {
            // Store some information before updating the element.
            Log.logData(analysis_data, Utils.generatePartingLine("="));
            Log.logData(analysis_data, "Save information -- element type update.");
            if(passing_variables.isEmpty()){
                passing_variables.add(null);
            }
            for(Value pv : passing_variables){
                saveDataStructureAndRelatedInfo(base_unit, element_type, pv, return_variable, identifier_variables,
                        passingMapVariableToInflowItem, passingStruVariableToSupportingObj, variableToField);
            }
            passing_variables.clear();
            passing_units.clear();
        }
    }

    public static int containTypedArrayInflowParam(InvokeExpr ie, Set<Integer> inflow_param_indices){
        if(ie == null || inflow_param_indices == null) return 0;

        for(int inflow_param_index : inflow_param_indices){
            Value inflow_param = ie.getArg(inflow_param_index);
            if(inflow_param.getType().toString().endsWith("TypedArray")){
                return 1;
            }
        }
        return 0;
    }

    public static int containParserInflowParam(InvokeExpr ie, Set<Integer> inflow_param_indices){
        if(ie == null || inflow_param_indices == null) return 0;

        for(int inflow_param_index : inflow_param_indices){
            Value inflow_param = ie.getArg(inflow_param_index);
            if(inflow_param.getType().toString().endsWith("XmlResourceParser")){
                return 1;
            }
        }
        return 0;
    }

    // base-unit and passingStruVariableToSupportingObj only work during analyzing current base method.
    public static Value confirmSupportingObjectFromCallee(BU base_unit, InvokeExpr call_ie, Body callee_body, List<Unit> passing_units,
                                                          Map<Value, Value> passingStruVariableToSupportingObj){
        if(call_ie == null) return null;
        String msg = "+ Confirm supporting object from callee: " + "\n--- Callee: " + call_ie.getMethod();
        Utils.logMsg(analysis_data, msg, "+");
        SootMethod callee = call_ie.getMethod();
        if("getKey_keySet_entrySet".contains(callee.getName())) return null; // We do not care about the Map-Key.
        // Map<String, Set<String>> r6
        // r6.put(r1, r2) or r6 = add(r6, r1, r2)
        // r5 = r6.entrySet
        // r4 = r5.getValue
        if(callee.getName().equals("getValue")) {
            Value map_variable = null;
            Value structure_variable = null;
            for(int i = passing_units.size(); i > 0; i--) {
                Unit pu = passing_units.get(i-1);
                InvokeExpr pu_ie = Utils.getInvokeOfUnit(pu);
                Value pu_base = Utils.getBaseOfInvokeExpr(pu_ie);
                if(pu_ie != null){
                    String pu_method_name = pu_ie.getMethod().getName();
                    if(pu_method_name.equals("entrySet")){
                        //out.println("=== pu_ie " + pu_ie);
                        map_variable = pu_base;
                        //out.println("=== pu_base " + pu_base);
                        if(passingStruVariableToSupportingObj!= null){
                            return passingStruVariableToSupportingObj.get(map_variable);
                        }
                    } else if(map_variable != null) {
                        if(pu_method_name.equals("put") && map_variable.equals(pu_base)) { // r6.put(r1, r2)
                            structure_variable = pu_ie.getArg(1); // r2
                        } else if(pu_method_name.equals("add") && pu_ie.getArg(0).equals(map_variable)) { // r6 = add(r6, r1, r2)
                            structure_variable = pu_ie.getArg(2); // r2
                        } else if ("addAll_putAll".contains(pu_method_name) && pu_ie.getArg(0).equals(map_variable)) { // r7.putAll(r6)
                            map_variable = pu_base;
                        }
                    }
                }
                if(structure_variable != null){
                    return confirmSupportingObjectByReturnVariable(callee_body, structure_variable);
                }
            }
            if(map_variable == null) {
                msg = "Cannot find the belonging map variable: " + call_ie;
                Utils.terminate(msg);
            }
            return null;
        }
        // Map<String, Set<String>> r6
        // r6.put(r1, r2) or r6 = add(r6, r1, r2)
        // r5 = r6.get(key)
        if(callee.getName().equals("get")) {
            Value call_base = Utils.getBaseOfInvokeExpr(call_ie);
            if(Utils.isStructuralVariable(call_base)) {
                if(passingStruVariableToSupportingObj != null) {
                    return passingStruVariableToSupportingObj.get(call_base);
                } else {
                    Value structural_variable = null;
                    for(int i = passing_units.size(); i>0; i--) {
                        Unit pu = passing_units.get(i-1);
                        InvokeExpr pu_ie = Utils.getInvokeOfUnit(pu);
                        Value pu_base = Utils.getBaseOfInvokeExpr(pu_ie);
                        if(pu_ie != null) {
                            String pu_method_name = pu_ie.getMethod().getName();
                            if (call_base.equals(pu_base)) { // r6.put(r1, r2)
                                if(pu_method_name.equals("put")) {
                                    structural_variable = pu_ie.getArg(1); // r2
                                } else if(pu_method_name.equals("add")) { // For non-map type variable.
                                    structural_variable = pu_ie.getArg(0);
                                }
                            } else if (pu_base == null && pu_method_name.equals("add") && pu_ie.getArg(0).equals(call_base)) { // r6 = add(r6, r1, r2)
                                structural_variable = pu_ie.getArg(2); // r2
                            } else if ("addAll_putAll".contains(pu_method_name) && pu_ie.getArg(0).equals(call_base)) { // r7.putAll(r6)
                                call_base = pu_base;
                            }
                            if(structural_variable != null) {
                                return confirmSupportingObjectByReturnVariable(callee_body, structural_variable);
                            }
                        }
                    }
                }
            }
            return null;
        }

        if(callee.isConcrete()){
            callee_body = callee.retrieveActiveBody();
            if(callee_body.getUnits().isEmpty()){
                System.out.println("=== Empty body: " + callee);
            }
        } else if (callee.isAbstract()) {
            SootMethod implemented_method = getImplementedMethodOfAbstractMethod(analysis_data, call_ie, base_unit);
            callee_body = implemented_method.retrieveActiveBody();
        } else if(callee.isNative()){
            System.out.println("Native method: " + callee);
        } else if (callee.isPhantom()){
            System.out.println("Phantom method: " + callee);
        }
        Value return_variable = Utils.getReturnVariable(callee_body);
        if(return_variable!=null && callee_body != null && !callee_body.getUnits().isEmpty()){
            return confirmSupportingObjectByReturnVariable(callee_body, return_variable);
        }
        return null;
    }


    // Since Array-type variable can get its element type directly, we won't care about it.
    // We never analyzed callee_body.
    public static Value confirmSupportingObjectByReturnVariable(Body callee_body, Value return_variable){
        if(return_variable == null || callee_body == null) return null;
        Log.logBody(callee_body, store_base_path);

        if(return_variable.getType().toString().endsWith("ParseResult")){
            return_variable = transferCorrectReturnVariable(return_variable, callee_body);
        }

        List<Unit> unit_list = Utils.bodyToList(callee_body);
        List<Unit> analyzed_units = new ArrayList<>();
        for(int i = unit_list.size() - 1 ; i >= 0; i--){ // Ensure the found supporting object is nearest the return statement.
            Unit unit = unit_list.get(i);
            analyzed_units.add(unit);
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                Value base = Utils.getBaseOfInvokeExpr(ie);
                if(ie!=null && ie.getMethod().getName().startsWith("empty")){ // $r1 = staticinvoke <java.util.Collections: java.util.List emptyList()>();
                    continue;
                }
                if(as.getLeftOp().equals(return_variable) || (base!=null && base.equals(return_variable))){
                    if(ie!=null){
                        String method_name = ie.getMethod().getName();
                        if(method_name.equals("add")){
                            if(Utils.isMapVariable(return_variable)){ // r1 = CollectionUtils.add(r1, r2, r3)
                                return ie.getArg(2); // Map-Value
                            }
                            if(base!=null){ // r1.add(r2)
                                return ie.getArg(0);
                            } else {
                                return ie.getArg(1); // r1 = CollectionUtils.add(r1, r2)
                            }
                        } else if (method_name.equals("put")) {
                            return ie.getArg(1);
                        } else if (method_name.equals("remove")) {
                            if(base != null) { // r1.remove(r2)
                                return ie.getArg(0);
                            } else {
                                return ie.getArg(1); // r1 = remove(r1, r2)
                            }
                        } else if (method_name.equals("addAll") || method_name.equals("putAll")){
                            return confirmSupportingObjectByReturnVariable(callee_body, ie.getArg(0));
                        } else if (as!=null){ // Still be a return value of a callee
                            List<Unit> unanalyzed_units = new ArrayList<>(CollectionUtils.disjunction(unit_list, analyzed_units));
                            return confirmSupportingObjectFromCallee(null, ie, callee_body, unanalyzed_units, null);
                        }
                    } else {
                        Value right_op = as.getRightOp();
                        if(right_op.getUseBoxes().isEmpty()) { // r1 = r0, return r1
                            return confirmSupportingObjectByReturnVariable(callee_body, right_op);
                        } else if(Utils.isFieldVariable(right_op)){ // r1 = r0.<mPermissions>
                            String field = "<" + right_op.toString().split("<")[1];
                            if(struFieldToSupportingObj.containsKey(field)){
                                return struFieldToSupportingObj.get(field);
                            }
                        } else if(right_op.toString().contains("(")){ // Still be a return value of a previous callee;
                            if(right_op.toString().contains("[")) return null; // r7 = newarray (byte)[$i1]
                            List<Unit> unanalyzed_units = new ArrayList<>(CollectionUtils.disjunction(unit_list, analyzed_units));
                            AssignStmt correct_as = transferCorrectAssignStmt(as, analysis_data, unanalyzed_units); // Find the invocation statement.
                            InvokeExpr correct_ie = Utils.getInvokeOfAssignStmt(correct_as);
                            if(correct_as == null || correct_ie == null){
                                String msg = "Transfer unsuccessfully, transferred AssignStmt: " + correct_as;
                                Utils.terminate(msg);
                            }
                            return confirmSupportingObjectFromCallee(null, correct_ie, callee_body, unanalyzed_units, null);
                        }
                    }
                }
            }
        }
        return null;
    }

    // Find the blocks that contains the noteworthy units and the first noteworthy unit (the start uint).
    public static Pair<List<Block>, Unit> findNoteworthyBlocksAndStartUnit(BU base_unit, Body body, CompleteBlockGraph cbg, List<Value> source_variables){
        List<Block> noteworthy_blocks = new ArrayList<>();
        Unit start_unit = null;
        Set<AssignStmt> source_defs = base_unit.getSourceDefs() != null ? base_unit.getSourceDefs().keySet() : null;
        for(Block block : cbg.getBlocks()){
            for(Unit unit : block){
                if(isNoteworthyUnit(base_unit, body, unit, source_variables, source_defs)){
                    if(!noteworthy_blocks.contains(block)){
                        noteworthy_blocks.add(block);
                        if(noteworthy_blocks.size() == 1) {
                            start_unit = unit;
                        }
                    }
                    break;
                }
            }
        }
        System.out.println("+ Noteworthy blocks: " + Utils.getBlockIds(noteworthy_blocks));
        out.println("+ Start unit: " + start_unit);
        Pair<List<Block>, Unit> out = new Pair<>(noteworthy_blocks, start_unit);
        return out;
    }
    public static void keepUsefulInfoForSkippedBlocks(CompleteBlockGraph cbg, BU base_unit, Body body, int start_block_id, List<Value> source_variables, Set<Value> identifier_variables,
                                                      Set<Value> null_variables, Map<Value, Value> newVariableToCopy, Map<Value, String> numericVariableToValue,
                                                      Map<Value, String> passingMapVariableToInflowItem, Map<Value, Value> passingStruVariableToSupportingObj,
                                                      Map<Value, String> stringVariableToElementType, Map<Value, String> variableToField){

        for(Block block : cbg.getBlocks()){
            if(block.getIndexInMethod() == start_block_id) {
                return;
            }
            for(Unit unit : block){
                storeUsefulInfo(base_unit, body, unit, source_variables, identifier_variables, null_variables, newVariableToCopy, numericVariableToValue,
                        passingMapVariableToInflowItem, passingStruVariableToSupportingObj, stringVariableToElementType, variableToField);
            }
        }
    }

    public static String getDataStructure(BU base_unit, Value passing_variable, Value return_variable, Set<Value> identifier_variable,
                                          Map<Value, String> passingMapVariableToInflowItem, Map<Value, Value> passingStruVariableToSupportingObj,
                                          Map<Value, String> variableToField){
        if (passing_variable == null) {
            return null;
        }

        passing_variable = Utils.getArrayVariable(passing_variable);
        String data_structure;
        // If the data structure is a field, store the whole field information.
        if (Utils.isFieldVariable(passing_variable)) {
            data_structure = "<" + passing_variable.toString().split("<")[1];
            String cls = confirmBelongingClsOfField(base_unit, passing_variable);
            if(cls!=null){
                data_structure += "_" + cls + "(BC)";
            }
        } else if (variableToField.containsKey(passing_variable)) {
            data_structure = variableToField.get(passing_variable);
        } else {
            data_structure = passing_variable.getType().toString();
        }
        // Flag return variable.
        if(return_variable!=null && return_variable.getType().toString().endsWith("ParseResult")){
            return_variable = transferCorrectReturnVariable(return_variable, base_unit.getBaseMethod().retrieveActiveBody());
        }
        if(passing_variable.equals(return_variable)){
            data_structure += "_return";
        }

        // Label this passing variable's type - suitable, unsuitable, unclear (need manual check)
        data_structure = labelPassingVariableType(base_unit, data_structure, passing_variable, identifier_variable, passingStruVariableToSupportingObj);

        if(Utils.isMapVariable(passing_variable)){ // For the Map value, we need know whether the key or value is reached.
            String item = passingMapVariableToInflowItem.get(passing_variable);
            if(item!=null) {
                data_structure += item;
            }else {
                String msg = "Cannot find the inflow item of the Map value: " + passing_variable;
                Utils.terminate(msg);
            }
        }
        return data_structure;
    }

    public static String getRelatedElementType(InvokeExpr ie, Map<Value, String> stringVariableToElementType){
        if(ie == null) return null;

        String method_name = ie.getMethod().getName();
        Value base = Utils.getBaseOfInvokeExpr(ie);
        String element_type = null;
        // Obtain element type.
        if (method_name.equals("equals")) {
            if (ie.getArg(0) instanceof StringConstant) { // parser.getName().equals(element_type)
                String s = ie.getArg(0).toString();
                if (!skip_names.contains(s) && ! s.startsWith("\"android.permission") && !s.startsWith("\"/")) {
                    element_type = s;
                }
            } else if (base != null && stringVariableToElementType!=null) { // element_type.equals(parser.getName())
                if (stringVariableToElementType.containsKey(base)) {
                    element_type = stringVariableToElementType.get(base);
                }
            }
        }
        return element_type;
    }

    public static String labelPassingVariableType(BU base_unit, String data_structure, Value passing_variable, Set<Value> identifier_variables,
                                                  Map<Value,Value> passingStruVariableToSupportingObj){
        SootClass declaring_cls = null;
        if(Utils.isMapVariable(passing_variable) || Utils.isDuplicationVariable(passing_variable)){
            if(passingStruVariableToSupportingObj.containsKey(passing_variable)) {
                Value supporting_obj = passingStruVariableToSupportingObj.get(passing_variable);
                storeStruFieldAndSupportingObj(passing_variable, supporting_obj);
                if(supporting_obj == null) {
                    if(passing_variable.getType() instanceof ArrayType){ // If the Array-type's corresponding supporting object is not recorded, get its declaring class directly.
                        ArrayType at = (ArrayType) passing_variable.getType();
                        declaring_cls = Utils.getDeclaringClassOfArrayElement(at);
                    } else {
                        data_structure += "_unclear"; // Need manual check.
                        return data_structure;
                    }
                } else if (supporting_obj.getUseBoxes().size() == 2) { // For the Pair variable.
                    Value var1 = supporting_obj.getUseBoxes().get(0).getValue();
                    Value var2 = supporting_obj.getUseBoxes().get(1).getValue();
                    List<Value> vars = new ArrayList<>();
                    vars.add(var1);
                    vars.add(var2);
                    int field_num = 0;
                    Set<String> field_names = new HashSet<>();
                    List<String> types = new ArrayList<>();
                    for(Value var : vars) {
                        if (!(var.getType() instanceof RefType) || Utils.isStringVariable(var)) {
                            field_num += 1;
                            types.add(var.getType().toString());
                        } else {
                            SootClass cls = ((RefType) var.getType()).getSootClass();
                            types.add(cls.getName());
                            Set<String> names = getFieldNamesOfDeclaringClass(base_unit, cls, var, analysis_data);
                            if (names.size() == 1) {
                                names = transferFieldNames(cls, names);
                            }
                            field_names.addAll(names);
                            field_num += field_names.size();
                        }
                    }
                    if(field_num > 1){ // The declaring class should have more than one field.
                        if(isIdentifierRelatedForPairVariable(base_unit, supporting_obj, identifier_variables) || field_names.contains("name")
                            || field_names.contains("tag") || field_names.contains("process")){ // The field names should contain the identifier.
                            data_structure += "_" + types + "(SO)_suitable";
                            return data_structure;
                        }
                    }
                    data_structure += "_" + types + "(SO)_unsuitable";
                    return data_structure;
                } else if (supporting_obj.getType() instanceof RefType) {
                    declaring_cls = ((RefType) supporting_obj.getType()).getSootClass();
                    if(declaring_cls.getName().endsWith("String")){
                        data_structure += "_" + declaring_cls + "(SO)_unsuitable";
                        return data_structure;
                    }
                }
                if(declaring_cls != null){
                    Set<String> field_names = getFieldNamesOfDeclaringClass(base_unit, declaring_cls, supporting_obj, analysis_data);
                    if (field_names.size() == 1) { // Further processing.
                        field_names = transferFieldNames(declaring_cls, field_names);
                    }
                    if (field_names.size() > 1){ // The declaring class should have more than one field.
                        if(field_names.contains("name") || field_names.contains("tag") || field_names.contains("process")){ // The field names should contain the identifier.
                            data_structure += "_" + declaring_cls + "(SO)_suitable";
                            return data_structure;
                        }
                    }
                }
            } else {
                String msg = "Cannot find the supporting object of the duplication variable: " + passing_variable + "\nType: " + passing_variable.getType() +
                        "\nDuplication variable set info: " + passingStruVariableToSupportingObj;
                Utils.terminate(msg);
            }
        }
        return data_structure + "_" + declaring_cls + "(SO)_unsuitable";
    }

    public static void saveDataStructureAndRelatedInfo(BU base_unit, String element_type, Value passing_variable, Value return_variable,
                                                       Set<Value> identifier_variable, Map<Value, String> passingMapVariableToInflowItem,
                                                       Map<Value, Value> passingStruVariableToSupportingObj, Map<Value, String> variableToField){
        String[] log_files = {analysis_data, method_data};
        String data_structure = getDataStructure(base_unit, passing_variable, return_variable, identifier_variable,
               passingMapVariableToInflowItem, passingStruVariableToSupportingObj, variableToField);
        // Merge the element types for this path and this base unit, respectively.
        String associated_element_type = getAssociatedElementType(base_unit.getAssociatedElementType(), element_type);
        // Save Info.
        base_unit.storeAssociatedElementTypeAndDataStructure(log_files, associated_element_type, data_structure);
        storeAssociatedElementTypeAndCorrespondingDataStructure(associated_element_type, data_structure);
    }

    // Associated element type: related to the current analyzed method and its parents.
    public static void storeAssociatedElementTypeAndCorrespondingDataStructure(String associated_element_type, String data_structure) {
        if(associated_element_type==null) return;

        /*if (data_structure == null){
            data_structure = "NUll";
        } else if (data_structure.endsWith("parsing.result.ParseResult")){ // The parse result of this element has not been solved completely.
            return;
        }*/

        Set<String> ds = associatedElementTypeToDataStructures.get(associated_element_type);
        if (ds == null) { // This key does not exist.
            ds = new HashSet<>();
            ds.add(data_structure);
            associatedElementTypeToDataStructures.put(associated_element_type, ds);
        } else {
            ds.add(data_structure);
        }
    }

    public static void storeStruFieldAndSupportingObj(Value v, Value supporting_obj){
        if(Utils.isFieldVariable(v)){
            String field = "<" + v.toString().split("<")[1];
            if(struFieldToSupportingObj.containsKey(field)){
                Value current_obj = struFieldToSupportingObj.get(field);
                if(current_obj == null && supporting_obj!=null) { // Update the null object to not null.
                    struFieldToSupportingObj.put(field, supporting_obj);
                } else if (current_obj!= null && supporting_obj != null) {
                    if(!current_obj.getType().equals(supporting_obj.getType())) {
                        String msg = "Structural field has been recorded.\n--- Current supporting object type " + current_obj.getType() +
                                "\n--- New supporting object type: " + supporting_obj.getType();
                        Utils.terminate(msg);
                    }
                }
            } else {
                struFieldToSupportingObj.put(field, supporting_obj);
            }
        }
    }

    public static void storeNumericVariableAndCorrespondingValue(BU base_unit, Body body, Unit unit, Map<Value, String> numericVariableToValue,
                                                                 Map<Value, String> stringVariableToElementType){
        if(base_unit == null || body == null || unit == null) return;

        AssignStmt as = null;
        if(unit instanceof AssignStmt) {
            as = (AssignStmt) unit;
        }
        if(as==null) return;

        Value left_op = as.getLeftOp();
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        List<ValueBox> vbs = as.getUseBoxes();
        if(Utils.isNumericVariable(left_op)){
            if(ie == null && vbs.size() == 1){
                Value right_op = as.getRightOp();
                if(right_op instanceof IntConstant){ // b1 = 2
                    numericVariableToValue.put(left_op, right_op.toString());
                } else if(Utils.isCopyStmt(as)){ // b1 = b2
                    String assign = numericVariableToValue.get(right_op);
                    numericVariableToValue.put(left_op, assign);
                }
            } else if(ie!=null) { // b1 is the return value of a method.
                String element_type = getRelatedElementType(ie, stringVariableToElementType);
                if(element_type!=null){
                    if(!confirmElementType(body, unit)){ // "receiver".equals("receiver")
                        String associated_element_type = base_unit.getAssociatedElementType();
                        if(associated_element_type != null) {
                            String[] associated_element_types = associated_element_type.split("_");
                            String least_element_type = associated_element_types[associated_element_types.length - 1];
                            if (element_type.equals(least_element_type)) {
                                numericVariableToValue.put(left_op, "1");
                            } else {
                                numericVariableToValue.put(left_op, "0");
                            }
                            String msg = "+ Update the numeric variable set: " + numericVariableToValue + "\n--- Unit: " + unit +
                                    "\n--- Element type variable set: " + stringVariableToElementType +
                                    "\n--- Least element type: " + least_element_type;
                            Utils.logMsg(analysis_data, msg, "+");
                        }
                    }
                } else {
                    numericVariableToValue.put(left_op, null);
                }
            }else{
                String s = vbs.get(0).getValue().toString();
                // Compute the concrete value when the assignment is an express.
                // Replace the Value with its concrete assignment.
                // Sort the list according to the Value name's length first in case that one value name is the prefix of another Value name.
                if(Utils.isExpress(s)) { // b1 = b2 | b3;
                    Collections.sort(vbs, new VBComparator());
                    int flag_compute = 1;
                    for (int j = 1; j < vbs.size(); j++) {
                        Value v = vbs.get(j).getValue();
                        String assign = numericVariableToValue.get(v);
                        if (assign == null) {
                            flag_compute = 0; // Cannot compute the value of this express because the concrete value of the numeric Value is unknown.
                            numericVariableToValue.put(left_op, null);
                            break;
                        }
                        s = s.replace(v.toString(), assign);
                    }
                    if (flag_compute == 1) {
                        ScriptEngineManager sem = new ScriptEngineManager();
                        ScriptEngine se = sem.getEngineByName("js");
                        try {
                            Object result = se.eval(s);
                            numericVariableToValue.put(left_op, result.toString());
                        } catch (ScriptException e) {
                            System.out.println(Utils.generatePartingLine("!"));
                            System.out.println("Computing Error: " + s);
                            System.out.println(Utils.generatePartingLine("!"));
                            throw new RuntimeException(e);
                        }
                    }
                } else if (vbs.size() == 2){
                    // The assignment involves data transformation.
                    if(s.startsWith("(")){ // i1 = (int) z0
                        String assign = numericVariableToValue.get(vbs.get(1).getValue());
                        numericVariableToValue.put(left_op, assign);
                    } else {
                        numericVariableToValue.put(left_op, null);
                    }
                } else {
                    numericVariableToValue.put(left_op, null);
                }
            }
        }
    }

    public static void storePassingStrucVariableToSupportingObj(Value passing_stru_var, Value supporting_obj, Map<Value, Value> newVariableToCopy,
                                                                Map<Value, Value> passingStruVariableToSupportingObj){
        if(passing_stru_var==null){
            return ;
        }
        // For the Array-type variable
        // r0[i1] => r0
        passing_stru_var = Utils.getArrayVariable(passing_stru_var);
        // For the addAll / putAll / multi-dimension array situation.
        // {r1 => r2}
        // r0 => r1 ==> r0 => r2
        while(passingStruVariableToSupportingObj.containsKey(supporting_obj)) {
            supporting_obj = passingStruVariableToSupportingObj.get(supporting_obj);
        }
        passingStruVariableToSupportingObj.put(passing_stru_var, supporting_obj);
        // If the passing duplicated-type variable is a newly constructed object, its copy also needs to be kept.
        if(newVariableToCopy!=null && newVariableToCopy.containsKey(passing_stru_var)){
            Value copy = newVariableToCopy.get(passing_stru_var);
            if(copy != null){
                passingStruVariableToSupportingObj.put(copy, supporting_obj);
            }
        }
    }

    // This statement is related to an element type.
    public static void storeStringVariableAndCorrespondingElementType(AssignStmt as, Map<Value, String> stringVariableToElementType){
        if(as == null) return;
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);

        if (ie == null && as.getUseBoxes().size()==1) {
            Value left_op = as.getLeftOp();
            Value right_op = as.getRightOp();
            if(right_op instanceof StringConstant) { // $r4 = "manifest"
                String element_type = right_op.toString();
                if (element_type.startsWith("\"/")) return;
                if (element_type.startsWith("\"android.permission")) return;
                if (skip_names.contains(element_type)) return;
                stringVariableToElementType.put(left_op, element_type);
                String msg = "+ Element type assignment: " + as;
                Utils.logMsg(analysis_data, msg, "+");
            } else if(stringVariableToElementType.containsKey(right_op)){ // $r3 = $r4
                String element_type = stringVariableToElementType.get(right_op);
                stringVariableToElementType.put(left_op, element_type);
                String msg = "+ Element type: " + as + " = " +  element_type;
                Utils.logMsg(analysis_data, msg, "+");
            } else if(stringVariableToElementType.containsKey(left_op)){ // This String value is re-defined.
                stringVariableToElementType.remove(left_op);
            }
        } else if(stringVariableToElementType.containsKey(as.getLeftOp())){ // This String value is re-defined.
            stringVariableToElementType.remove(as.getLeftOp());
        }
    }

    public static void storeUsefulInfo(BU base_unit, Body body, Unit unit, List<Value> source_variables, Set<Value> identifier_variables,
                                       Set<Value> null_variables, Map<Value, Value> newVariableToCopy, Map<Value, String> numericVariableToValue,
                                       Map<Value, String> passingMapVariableToInflowItem, Map<Value, Value> passingStruVariableToSupportingObj,
                                       Map<Value, String> stringVariableToElementType, Map<Value, String> variableToField){
        if(unit==null) return;

        AssignStmt as = null;
        if(unit instanceof AssignStmt){
            as = (AssignStmt) unit;
        }
        if(as == null) return;

        if (Utils.hasCopyOfVars(as, source_variables)) {
            Value source_var = as.getRightOp();
            Value copy = as.getLeftOp();
            if(!source_variables.contains(copy)) {
                source_variables.add(copy);
            }
            // For the situation that the source variable is structural type.
            if(passingStruVariableToSupportingObj.containsKey(source_var)){
                Value supporting_obj = passingStruVariableToSupportingObj.get(source_var);
                storePassingStrucVariableToSupportingObj(copy, supporting_obj, newVariableToCopy, passingStruVariableToSupportingObj);
            }
            // For the situation that the source variable is Map-type.
            if(passingMapVariableToInflowItem.containsKey(source_var)){
                String inflow_map_item = passingMapVariableToInflowItem.get(as.getRightOp());
                storePassingMapVariableAndCorrespondingInflowItem(copy, inflow_map_item, newVariableToCopy, passingMapVariableToInflowItem);
            }
            // For the situation that the source variable is identifier-related.
            if(identifier_variables.contains(source_var)){
                identifier_variables.add(copy);
            }
        }
        storeNewVariableAndCorrespondingCopy(as, newVariableToCopy);
        storeNullVariable(as, null_variables, newVariableToCopy);
        storeNumericVariableAndCorrespondingValue(base_unit, body, unit, numericVariableToValue, stringVariableToElementType);
        storeStringVariableAndCorrespondingElementType(as, stringVariableToElementType);
        storeVariableAndCorrespondingField(as, base_unit, variableToField);
        /*String msg = "Update the useful info:" + "\nSource variable set: " + source_variables + "\nNew variable set: " + newVariableToCopy +
                "\nElement type-related variable set: " + stringVariableToElementType + "\nNumeric variable set: " + numericVariableToValue +
                "\nField-related variable set: " + variableToField;
        Utils.logMsg(analysis_data, msg, "+");*/
    }

    // $r8 = interfaceinvoke $r4.<android.content.pm.parsing.result.ParseInput: android.content.pm.parsing.result.ParseResult success(java.lang.Object)>(r5);
    // return $r8;
    public static Value transferCorrectReturnVariable(Value return_variable, Body body){
        for(Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                if(as.getLeftOp().equals(return_variable)){
                    InvokeExpr i = Utils.getInvokeOfAssignStmt(as);
                    if(i!=null && i.getMethod().getName().equals("success")){
                        return_variable = i.getArg(0); // r5
                    }
                }
            }
        }
        return return_variable;
    }

    public static Set<String> transferFieldNames(SootClass declaring_cls, Set<String> field_names){
        if(field_names.size()!=1) return field_names;

        SootField field = null;
        SootClass cls = null;
        for(SootField sf : declaring_cls.getFields()){
            if(sf.getName().equals("CREATOR")) continue;
            field = sf;
        }
        Type type = field.getType();
        if(type.toString().contains("[")) {
            ArrayType at = (ArrayType) type;
            cls = Utils.getDeclaringClassOfArrayElement(at);
        } else if (type instanceof RefType) {
            if(type.toString().endsWith("String") || Utils.isMapField(field) || Utils.isDuplicationField(field)) return field_names;
            cls = ((RefType) type).getSootClass();
        }
        field_names = getFieldNamesOfDeclaringClass(null, cls, null, null);
        return field_names;
    }

    // XmlResourceParser => XmlResourceParser + Resources (special method) || Resources (un-special method)
    public static void transferSourceVarSet(BU base_unit, Body body, boolean special_method, List<Value> source_variables){
        if(source_variables == null || body == null) return;

        if(!source_variables.get(0).getType().toString().equals("android.content.res.XmlResourceParser")){
            source_variables.clear();
            return;
        }

        List<Value> new_source_variables = new ArrayList<>();
        Map<AssignStmt, String> sourceDefTOElementType = new HashMap<>();
        //$r8 = virtualinvoke $r2.<android.content.res.Resources: android.content.res.TypedArray obtainAttributes(android.util.AttributeSet,int[])>($r3, r7);
        for(Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                if(ie!=null && ie.getMethod().getName().equals("obtainAttributes")){
                    if(!hasParamsOfInvokeExpr(base_unit, ie, analysis_data, source_variables).isEmpty()){
                        Value new_source_variable = as.getLeftOp();
                        if(!new_source_variables.contains(new_source_variable)) {
                            new_source_variables.add(new_source_variable);
                        }
                        sourceDefTOElementType.put(as, null);
                    }
                }
            }
        }
        if(!new_source_variables.isEmpty()) {
            if (special_method) { // The method implements multiple analysis method.
                source_variables.addAll(new_source_variables);
            } else {
                source_variables.clear();
                source_variables.addAll(new_source_variables);
                // Set the definitions of this new source variables.
                base_unit.setSourceDefs(sourceDefTOElementType);
            }
        } else if(!special_method){
            source_variables.clear();
        }
    }

    public static void updatePassingVariableSet(Value outflow_variable, List<Value> inflow_passing_variables, List<Value> passing_variables, 
                                                List<Value> source_variables, Map<Value, Value> newValueToCopy, String callee_name){
        // Update the passing variable set.
        if(!inflow_passing_variables.isEmpty()) {
            // Remove the inflow passing variable.
            for(Value var : inflow_passing_variables) {
                if (var.getType().toString().endsWith("parsing.result.ParseResult") && !callee_name.equals("getResult")) {
                    Log.logData(analysis_data, "--- Cannot update the passing variable: " + var);
                    return;
                }
                removeVariable(var, passing_variables, newValueToCopy);
            }
        }
        // Add the outflow variable.
        addVariable(outflow_variable, passing_variables, newValueToCopy);
        Log.logData(analysis_data, "--- Update the passing variable set: " + passing_variables);
        // The source variable has been re-defined.
        if(source_variables.contains(outflow_variable)){
            source_variables.remove(outflow_variable);
            Log.logData(analysis_data, "--- Remove re-defined source variable: " + outflow_variable);
            Log.logData(analysis_data, "--- Update the source_variable_set: " + source_variables);
        }
    }

    // Map-Value, Pair, Set, List, Stack, Queue
    public static void updatePassingStructuralVariableInfo(AssignStmt as, BU base_unit, InvokeExpr ie, String method_name, Value outflow_variable,
                                                           Set<Integer> inflow_param_indices, List<Value> inflow_source_variables,
                                                           List<Value> inflow_passing_variables, Map<Value, Value> newVariableToCopy,
                                                           List<Unit>passing_units, Map<Value, Value> passingStruVariableToSupportingObj) {
        if(!Utils.isStructuralVariable(outflow_variable)) return;

        Value support_obj = null;
        // For the Map-type value, we care about its Value type.
        if("add_put".contains(method_name) && Utils.isMapVariable(outflow_variable)) {
            if (method_name.equals("add")) {
                if (inflow_param_indices.contains(2)) {
                    support_obj = ie.getArg(2); // Map-Value
                }
            } else if (method_name.equals("put")) {
                if (inflow_param_indices.contains(1)) {
                    support_obj = ie.getArg(1); // Map-Value
                }
            }
        } else if(Utils.isPairVariable(outflow_variable) && as != null){
            // $r4 = staticinvoke <android.util.Pair: android.util.Pair create(java.lang.Object,java.lang.Object)>($r1, $r2)
            if(method_name.equals("create")){
                support_obj = as.getRightOp();
            }
        } else {
            List<Value> inflow_vars = Utils.deepCopy(inflow_source_variables);
            for(Value v : inflow_passing_variables){
                if(inflow_vars.contains(v)) continue;;
                inflow_vars.add(v);
            }
            if(inflow_vars.contains(outflow_variable)) {
                inflow_vars.remove(outflow_variable);
            }
            Value inflow_variable = null;
            if(inflow_vars.size() == 1){
                inflow_variable = inflow_vars.get(0);
            } else {
                String msg = "Special duplication item, more than one inflow variables. " + "\nInflow variables : " +
                        inflow_source_variables + ", " + inflow_passing_variables;
                Utils.terminate(msg);
            }
            if(inflow_variable == null){
                exit(0);
            }
            if(passingStruVariableToSupportingObj.containsKey(inflow_variable)){
                support_obj = passingStruVariableToSupportingObj.get(inflow_variable);
            } else if (ie == null && as.getRightOp().toString().contains("(")) { // The structure variable is the return value of the previous callee.
                if(Utils.isArrayVariable(outflow_variable)){
                    support_obj = null; // Get the Array element type directly later.
                }else {
                    // Find the callee.
                    AssignStmt correct_as = transferCorrectAssignStmt(as, analysis_data, passing_units);
                    InvokeExpr correct_ie = Utils.getInvokeOfAssignStmt(correct_as);
                    if (correct_as == null || correct_ie == null) {
                        String msg = "Transfer unsuccessfully, transferred AssignStmt: " + correct_as;
                        Utils.terminate(msg);
                    }
                    method_name = correct_ie.getMethod().getName();
                    support_obj = confirmSupportingObjectFromCallee(base_unit, correct_ie, null, passing_units, passingStruVariableToSupportingObj);
                }
            } else if (inflow_variable.equals(Utils.getBaseOfInvokeExpr(ie))) { // The structure variable is the return value of the callee.
                if(Utils.isArrayVariable(outflow_variable)) {
                    support_obj = null; // Get the Array element type directly later.
                } else {
                    support_obj = confirmSupportingObjectFromCallee(base_unit, ie, null, passing_units, passingStruVariableToSupportingObj);
                }
            } else {
                support_obj = inflow_variable;
            }
            if(support_obj == null){
                if(!(Utils.isArrayVariable(outflow_variable) || Utils.isMapVariable(outflow_variable)) &&
                        !"keySet_getKey_entrySet_get_getValue".contains(method_name)) {
                    String msg = "Cannot confirm the supporting object, may confirm it manually: " + as;
                    Utils.logMsg(analysis_data, msg, "!");
                }
            }
        }
        storePassingStrucVariableToSupportingObj(outflow_variable, support_obj, newVariableToCopy, passingStruVariableToSupportingObj);
        Log.logData(analysis_data, "--- Update the structural variable info: " + passingStruVariableToSupportingObj);
    }

    // Find the method for starting to parse the AndroidManifest.xml
    public static void findEntryBaseUnits() {
        List<SootMethod> methods = Utils.getMethodsOfClass(parsing_class);
        for (SootMethod sm : methods) {
            if (sm.isConcrete()) {
                Body body = sm.retrieveActiveBody();
                List<Value> source_variables = new ArrayList<>();
                Map<AssignStmt, String> sourceDefToElementType = new HashMap<>();
                for (Unit unit : body.getUnits()) {
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        InvokeExpr callee = Utils.getInvokeOfAssignStmt(as);
                        if (callee != null) {
                            // find the entry base unit.
                            String calleeName = callee.getMethod().getName();
                            if (calleeName.equals("openXmlResourceParser")) {
                                for (Value v : callee.getArgs()) {
                                    if (v instanceof StringConstant) {
                                        String parameterName = v.toString();
                                        if (parameterName.equals("\"AndroidManifest.xml\"")) {
                                            Value source_variable = as.getLeftOp();
                                            if (!source_variables.contains(source_variable)) {
                                                source_variables.add(source_variable);
                                            }
                                            sourceDefToElementType.put(as, null);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if(!source_variables.isEmpty()){
                    BU base_unit = new BU(sm, source_variables);
                    base_unit.setSourceDefs(sourceDefToElementType);
                    base_units.offer(base_unit);
                }
            }
        }
    }

    public static void dataFlowAnalysisForBaseUnit(BU base_unit){
        SootMethod base_method = base_unit.getBaseMethod();
        Body body = null;
        if (base_method.isConcrete()) {
            body = base_method.retrieveActiveBody();
        } else {
            Utils.printPartingLine("!");
            System.out.println("This method does not have a body: " + base_method);
            if(base_method.isNative()) {
                System.out.println("Native method.");
            } else if(base_method.isPhantom()) {
                System.out.println("Phantom method.");
            }
            Utils.printPartingLine("!");
            exit(0);
        }

        String base_unit_sig = generateSignatureOfBaseUnit(base_unit).split("&")[1];
        Map<Value, Value> newVariableToCopy = new HashMap<>(); // The newly constructed object and its copy.
        // Initialize some information.
        List<Value> source_variables = Utils.deepCopy(base_unit.getSourceVariables());
        Set<Value> identifier_variables = new HashSet<>(); // The variable related to an identifier (name or tag or process).
        Set<Value> null_variables = new HashSet<>(); // The variable with null constant.
        Map<Value, String> passingMapVariableToInflowItem = new HashMap<>(); // The passing Map-type variable's corresponding inflow item info.
        Map<Value, Value> passingStruVariableToSupportingObj = new HashMap<>(); // The passing structural variable's supporting object info.
        Map<Value, String> numericVariableToValue = new HashMap<>(); // The concrete value of all numeric variables (iX, bX, zX).
        Map<Value, String> stringVariableToElementType = new HashMap<>(); // The variable whose value is String.
        Map<Value, String> variableToField = new HashMap<>(); // The variable related to a field.
        initializeUsefulInfo(base_unit, body, source_variables, null, identifier_variables, null_variables, numericVariableToValue,
                passingMapVariableToInflowItem, passingStruVariableToSupportingObj, stringVariableToElementType, variableToField);

        Utils.printPartingLine("=");
        System.out.println("+ Base method: " + base_method.getName() + "\n+ Base-unit sig: " + base_unit_sig);
        System.out.println("+ Source variables: " + source_variables);
        System.out.println("+ Associated element type: " + base_unit.getAssociatedElementType());
        //Log.
        Log.logData(analysis_data, "+ Source variables: " + source_variables + "\n+ Associated element type: " +
                base_unit.getAssociatedElementType());

        // Construct the block graph.
        CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        Log.logBody(body, store_base_path);
        Log.logCBG(cbg, store_base_path);

        // For parsing the manifest file, there are three parsing ways:
        // (1) treats the element parser as a whole and gets its parse result.
        // (2) gets the attributes of the element parser.
        // (3) special methods combine (1) & (2).
        boolean special_method = isSpecialMethod(base_method.getName());
        if(special_method){
            transferSourceVarSet(base_unit, body, true, source_variables);
            String msg = "+ Special method, transform the source variable: " + source_variables;
            Utils.logMsg(analysis_data, msg, "+");
            System.out.println("Special method, Transform the source variable: " + source_variables);
        }
        // Find noteworthy blocks.
        System.out.println("Find noteworthy blocks and the start unit...");
        Pair<List<Block>, Unit> noteworthy_info = findNoteworthyBlocksAndStartUnit(base_unit, body, cbg, source_variables);
        List<Block> noteworthy_blocks = noteworthy_info.getO1();
        Unit start_unit = noteworthy_info.getO2();
        if(noteworthy_blocks.isEmpty()){
            if(special_method){
                String msg = "Cannot find the noteworthy blocks of the special method: " + base_method.getSignature();
                Utils.terminate(msg);
            }
            // These methods do not implement the general analysis methods.
            // We need transform the source variable.
            transferSourceVarSet(base_unit, body, false, source_variables);
            System.out.println("Cannot find the noteworthy blocks, transform the source variable: " + source_variables);
            String msg = "+ Cannot find the noteworthy block, transform the source variable :" + source_variables;
            Utils.logMsg(analysis_data, msg, "+");
            // Find noteworthy blocks again.
            noteworthy_info = findNoteworthyBlocksAndStartUnit(base_unit, body, cbg, source_variables);
            noteworthy_blocks = noteworthy_info.getO1();
            start_unit = noteworthy_info.getO2();
            if(noteworthy_blocks.isEmpty()){
                String[] log_files = {analysis_data, method_data};
                Log.logData(analysis_data, Utils.generatePartingLine("="));
                Log.logData(analysis_data, "Still cannot find, this method does not need to analyze.");
                base_unit.storeAssociatedElementTypeAndDataStructure(log_files, null, null);
                msg = "Cannot find the noteworthy block. Analyze the next base unit.";
                Utils.printMsg(msg, "!");
                return;
            }
        }
        // Confirm analysis model.
        out.println("Confirm analysis model ...");
        int path_sensitive = 1;
        int start_block_id = cbg.getHeads().get(0).getIndexInMethod(); // Analysis mode 0 -- the first noteworthy block; 1 -- the first block; 2 -- the LCA block.
        int analysis_model = confirmAnalysisModel(base_method.getName(), cbg, noteworthy_blocks);
        out.println("+ Analysis model (0: flow-insensitive, 1: from the head block, 2: from the LCA block): " + analysis_model);
        if(analysis_model != 1) {
            if (analysis_model == 0) { // Flow-insensitive analysis.
                base_unit.setStartUnit(start_unit); // Set the start unit (the first noteworthy unit). For path-sensitive analysis, different path may have different start unit.
                start_block_id = noteworthy_blocks.get(0).getIndexInMethod();
                List<Integer> path = new ArrayList<>();
                for (int i = start_block_id;  i < cbg.getBlocks().size(); i++) {
                    path.add(i);
                }
                Graph.paths.add(path);
                Graph.path_num = 1;
                path_sensitive = 0;
            } else { // Start analyzing from the LCA.
                start_block_id = Graph.getLeastCommonAncestorOfBlocks(noteworthy_blocks);
            }
            if(start_block_id == -1) {
                String msg = "Illegal start block id.";
                Utils.terminate(msg);
            }
            // Since in mode 0 / 2, we will not start analysis from the head block.
            // We need to store some useful info before we skip some blocks.
            keepUsefulInfoForSkippedBlocks(cbg, base_unit, body, start_block_id, source_variables, identifier_variables, null_variables,
                    newVariableToCopy, numericVariableToValue, passingMapVariableToInflowItem, passingStruVariableToSupportingObj,
                    stringVariableToElementType, variableToField);
        }

        System.out.println("+ Start block id: " + start_block_id + "\n+ Parameters: " + base_unit.getParameters() +
                "\n+ Numeric variables: " + numericVariableToValue + "\n+ Element type variables: " + stringVariableToElementType +
                "\n+ Field variables: " + variableToField + "\n+ Null variables: " + null_variables);

        // Log data.
        Log.logData(analysis_data, "+ Base method parameters:" + base_unit.getParameters() + "\n+ Start block id: " + start_block_id +
                "\n+ Identifiers: " + identifier_variables + "\n+ Null variables:" + null_variables + "\n+ Passing Map variables: " +
                passingMapVariableToInflowItem + "\n+ Passing structure variable: " + passingStruVariableToSupportingObj + "\n+ Numeric variables: " +
                numericVariableToValue + "\n+ Element type variables: " + stringVariableToElementType + "\n+ Field variables: " + variableToField);

        out.println("Start analyzing ...");
        int total_path_num = Graph.path_num;
        out.println("+ Total path num needed to analyze: " + total_path_num);
        Graph.path_num = 0; // Reset the path number.
        if (Utils.hasDuplicatedItems(Graph.paths)) {
            String msg = "Exist duplicated paths.";
            Utils.terminate(msg);
        } else {
            System.out.println("No duplicated paths.");
        }

        //Log data.
        Log.logData(method_data, Utils.generatePartingLine("#"));
        Log.logData(method_data, "+ Method: " + base_method.getSignature() + "\n+ Base-unit sig: " + base_unit_sig);

        int analyzed_path_num = 0;
        List<String> generated_BU_sigs = new ArrayList<>();  // Avoid duplicated generating, because multiple paths may involve the same methods.
        while(!Graph.paths.isEmpty()) {
            List<Integer> path = Graph.paths.get(0);
            analyzed_path_num+=1;
            Graph.paths.remove(0);
            Log.logData(analysis_data, Utils.generatePartingLine(">"));
            Log.logData(analysis_data, "+ Path " + analyzed_path_num +": " + path);
            dataFlowAnalysisForPath(base_unit, body, path_sensitive, cbg.getBlocks(), generated_BU_sigs, path, source_variables, identifier_variables,
                    null_variables, newVariableToCopy, numericVariableToValue, passingMapVariableToInflowItem, passingStruVariableToSupportingObj,
                    stringVariableToElementType, variableToField);
            if(analyzed_path_num == total_path_num|| analyzed_path_num % 1000 == 0) {
                System.out.println("Analyzed path num: " + analyzed_path_num);
            }
        }
    }

    // For an element in the app's manifest,
    // the system will invoke the corresponding parsing method to parse it,
    // and get its parsing result.
    // For example: for the element <permission>, its parse method is parsePermission,
    // the parsing result is ParsedPermission.
    // So, during analyzing, we treat the tainted / entry value as a whole,
    // ignore the part (ie., the attribute) of it.
    // The attributes are wrapped in the parsing result.
    public static void dataFlowAnalysisForPath(BU base_unit, Body body, int path_sensitive, List<Block> blocks, List<String> generated_BU_sigs,
                                               List<Integer> path, List<Value> source_variables, Set<Value> identifier_variables, Set<Value> null_variables,
                                               Map<Value, Value> newVariableToCopy, Map<Value, String> numericVariableToValue,
                                                Map<Value, String> passingMapVariableToInflowItem, Map<Value, Value> passingStruVariableToSupportingObj,
                                               Map<Value, String> stringVariableToElementType, Map<Value, String> variableToField) {
        String base_method_name = base_unit.getBaseMethod().getName();
        Set<AssignStmt> source_defs = base_unit.getSourceDefs() != null ? base_unit.getSourceDefs().keySet() : null;
        Unit start_unit = base_unit.getStartUnit();

        // Copy info.
        // Specific to this path.
        List<Value> source_variables_path = Utils.deepCopy(source_variables);
        Set<Value> identifier_variables_path = Utils.deepCopy(identifier_variables);
        Set<Value> null_variables_path = Utils.deepCopy(null_variables);
        Map<Value, Value> newVariableToCopy_path = Utils.deepCopy(newVariableToCopy);
        Map<Value, String> numericVariableToValue_path = Utils.deepCopy(numericVariableToValue);
        Map<Value, String> passingMapVariableToInflowItem_path = Utils.deepCopy(passingMapVariableToInflowItem);
        Map<Value, Value> passingStruVariableToSupportingObj_path = Utils.deepCopy(passingStruVariableToSupportingObj);
        Map<Value, String> stringVariableToElementType_path = Utils.deepCopy(stringVariableToElementType);
        Map<Value, String> variableToField_path = Utils.deepCopy(variableToField);


        String element_type = null; // The element type related to this path.
        Value return_variable = null; // A path has 0 or 1 return value.
        List<Value> passing_variables = new ArrayList<>(); // The variables into which the data stored in the source variables flow.
        List<Unit> passing_units = new ArrayList<>(); // The statements that trigger the variable propagation.

        int flag_analysis = 0;
        Value element_type_boolean = null; // The boolean variable related to an element type comparison.


        for (int i = 0; i< path.size(); i++) {
            int block_id = path.get(i);
            Block block = blocks.get(block_id);
            for (Unit unit : block) {
                flag_analysis = canStartAnalysis(flag_analysis, start_unit, path_sensitive, unit, source_defs);
                if(flag_analysis == 0) {
                    // Store useful info before skipping this unit.
                    storeUsefulInfo(base_unit, body, unit, source_variables_path, identifier_variables_path, null_variables_path, newVariableToCopy_path,
                            numericVariableToValue_path, passingMapVariableToInflowItem_path, passingStruVariableToSupportingObj_path,
                            stringVariableToElementType_path, variableToField_path);
                    continue;
                }

                InvokeExpr ie = null;
                Value base = null;
                SootMethod callee = null;
                String callee_name = "NULL";

                int need_analysis = 0;
                int assignStmt = 0;
                int flag_attribute = 0;
                List<Value> inflow_source_variables = new ArrayList<>(); // The source variables that flow into this statement.
                List<Value> inflow_passing_variables = new ArrayList<>(); // The passing variables that flow into this statement.

                // Get the return variable.
                if(unit instanceof ReturnStmt){
                    ReturnStmt rs = (ReturnStmt) unit;
                    return_variable = rs.getOp();
                    continue;
                }

                // Filter wrong paths.
                if(path_sensitive == 1) {
                    if (unit instanceof LookupSwitchStmt) {
                        LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                        Value case_value = lss.getKey();
                        boolean wrong_path = isWrongPathForSwitchStmt(analysis_data, blocks, path, i, lss, case_value, numericVariableToValue_path);
                        if (wrong_path) {
                            String msg = "+ Wrong path, stop analyzing!";
                            Utils.logMsg(analysis_data, msg, "!");
                            return;
                        }
                    }else if (unit instanceof IfStmt) {
                        IfStmt is = (IfStmt) unit;
                        boolean wrong_path = isWrongPathForIfStmt(blocks, path, i, is, identifier_variables_path, null_variables_path, numericVariableToValue_path);
                        if (wrong_path) {
                            String msg = "+ Wrong path, stop analyzing!" + "\n--- " + is + "\n--- Null variable set: " + null_variables +
                                    "\n--- Numeric variable set: " + numericVariableToValue_path;
                            Utils.logMsg(analysis_data, msg, "!");
                            return;
                        }
                        if(needUpdateElementType(blocks, path, i, is, element_type_boolean)){ // The recorded element type is not associated with this path.
                            element_type = null;
                            String msg = "+ The recorded element type is not associated with this path, update it to null." +
                                    "\n--- Unit: " + is;
                            Utils.logMsg(analysis_data, msg, "+");
                        }
                        continue;
                    }
                }

                // A statement needs to be analysed only if it contains the entry / tainted value.
                if (unit instanceof AssignStmt) {
                    assignStmt = 1;
                    AssignStmt as = (AssignStmt) unit;
                    ie = Utils.getInvokeOfAssignStmt(as);
                    inflow_source_variables = hasRightVarsOfAssignStmt(as, base_unit, analysis_data, source_variables_path);
                    inflow_passing_variables = hasRightVarsOfAssignStmt(as, base_unit, analysis_data, passing_variables);
                    if(!inflow_source_variables.isEmpty() || !inflow_passing_variables.isEmpty()){
                        need_analysis = 1;
                    }
                    // This source / passing value has been re-defined.
                    if (need_analysis == 0) {
                        adjustVariableSetIfVariableRedefined(as, base_unit, element_type, ie, return_variable, passing_units, passing_variables,
                                source_variables_path, identifier_variables_path, source_defs, newVariableToCopy_path,
                                passingMapVariableToInflowItem_path, passingStruVariableToSupportingObj_path,
                                variableToField_path);
                    }
                    // System.out.println("--- " + as);
                    // Store useful information.
                    storeUsefulInfo(base_unit, body, unit, source_variables_path, identifier_variables_path, null_variables_path, newVariableToCopy_path,
                            numericVariableToValue_path, passingMapVariableToInflowItem_path, passingStruVariableToSupportingObj_path,
                            stringVariableToElementType_path, variableToField_path);
                } else if (unit instanceof InvokeStmt) {
                    ie = ((InvokeStmt) unit).getInvokeExpr();
                    base = Utils.getBaseOfInvokeExpr(ie);
                    callee_name = ie.getMethod().getName();
                    inflow_source_variables = hasParamsOfInvokeExpr(base_unit, ie, analysis_data, source_variables_path);
                    inflow_passing_variables = hasParamsOfInvokeExpr(base_unit, ie, analysis_data, passing_variables);
                    if(!inflow_source_variables.isEmpty() || !inflow_passing_variables.isEmpty()) {
                        need_analysis = 1;
                    } else if(callee_name.equals("toArray")){
                        if(source_variables_path.contains(base)){
                            inflow_source_variables.add(base);
                            need_analysis = 1;
                        } else if (passing_variables.contains(base)){
                            inflow_passing_variables.add(base);
                            need_analysis = 1;
                        }
                    }
                }

                if (ie != null) {
                    callee = ie.getMethod();
                    callee_name = callee.getName();
                    base = Utils.getBaseOfInvokeExpr(ie);
                }

                // Get the element type.
                String new_element_type = getRelatedElementType(ie, stringVariableToElementType_path);
                if (new_element_type != null){
                    if(!confirmElementType(body, unit)){
                        String msg = "+ Illegal element type: " + new_element_type;
                        Utils.logMsg(analysis_data, msg, "!");
                        continue;
                    }
                    // Record the boolean variable that stores the element type comparison result.
                    element_type_boolean = ((AssignStmt) unit).getLeftOp();
                    if(!(element_type_boolean.getType() instanceof BooleanType)) {
                        String msg = "Special element type comparison: " + unit;
                        Utils.terminate(msg);
                    }
                    if(new_element_type.equals(element_type)) continue;
                    String msg = "+ Unit: " + unit + "\n--- Update the element type: " + element_type + " => " + new_element_type;
                    Utils.logMsg(analysis_data, msg, "+");
                    // Save information before update the element type.
                    // Have solved one element case.
                    // Or have tainted some values that irrelevant to this element.
                    adjustVariableSetIfElementTypeUpdate(base_unit, element_type, return_variable, identifier_variables_path, passing_units, passing_variables,
                            passingMapVariableToInflowItem_path, passingStruVariableToSupportingObj_path, variableToField_path);
                    // Update the element type.
                    element_type = new_element_type;
                    continue;
                } else { // Reset the element type variable if it is re-defined;
                    if(assignStmt == 1){
                        AssignStmt as = (AssignStmt) unit;
                        if(isLeftVarOfAssignStmt(as, element_type_boolean)){
                            element_type_boolean = null;
                        }
                    }
                }

                if (need_analysis == 0){
                    continue;
                }

                Log.logData(analysis_data, Utils.generatePartingLine("="));
                Log.logData(analysis_data, "+ Unit: " + unit);
                if (!inflow_source_variables.isEmpty()) {
                    Log.logData(analysis_data, "--- Inflow source variables: " + inflow_source_variables);
                }
                if(!inflow_passing_variables.isEmpty()){
                    Log.logData(analysis_data, "--- Inflow passing variables: " + inflow_passing_variables);
                }

                // If the source / passing value is passed in the callee, this callee is tainted.
                Set<Integer> inflow_param_indices = getInflowParamIndices(base_unit, ie, analysis_data, inflow_passing_variables, inflow_source_variables);
                if(!inflow_param_indices.isEmpty()){
                    Log.logData(analysis_data, "--- Inflow callee.");
                    int flag_array = containTypedArrayInflowParam(ie, inflow_param_indices);
                    if(canSkipForInflowParameter(base, callee, callee_name, flag_array)){
                        Log.logData(analysis_data, "--- Can skip, pass.");
                        continue;
                    }
                    if(callee.isConstructor()){
                        if(base != null){
                            // Update the passing variable set.
                            Value outflow_variable = base;
                            updatePassingVariableSet(outflow_variable, inflow_passing_variables, passing_variables, source_variables_path,
                                    newVariableToCopy_path, callee_name);
                            passing_units.add(unit);
                            continue;
                        }
                    }
                    // The add / put method is related to a Map value.
                    // For a Map value, we need know whether the tainted position is the key or the value.
                    if ("add_addAll_put_putAll".contains(callee_name)) { // add(tainted_value), put(tainted_value)
                        // r1.add(r2)
                        // r2 => r1
                        if (base != null) {
                            Value outflow_variable = base;
                            // Update the Map-type variable information.
                            updatePassingMapVariableInfo(null, ie, analysis_data, callee_name, outflow_variable, identifier_variables_path,
                                    inflow_param_indices, passing_units, newVariableToCopy_path, passingMapVariableToInflowItem_path);
                            // Update the structural type variable info.
                            updatePassingStructuralVariableInfo(null, base_unit, ie, callee_name, outflow_variable, inflow_param_indices,
                                    inflow_source_variables, inflow_passing_variables, newVariableToCopy_path, passing_units,
                                    passingStruVariableToSupportingObj_path);
                            // Update the passing variable set.
                            updatePassingVariableSet(outflow_variable, inflow_passing_variables, passing_variables, source_variables_path,
                                    newVariableToCopy_path, callee_name);
                            passing_units.add(unit);
                            continue;
                        }
                    }
                    // java.lang.System: void arraycopy(java.lang.Object,int,java.lang.Object,int,int)>(r11, 0, r13, 1, $i1)
                    // r11 => r13
                    if(callee_name.equals("arraycopy")){
                        if(!inflow_param_indices.contains(0)) {
                            Log.logData(analysis_data, "--- No data flow, pass");
                            continue;
                        }
                        Value outflow_variable = ie.getArg(2);
                        // Update the duplication-type variable info.
                        updatePassingStructuralVariableInfo(null, base_unit, ie, callee_name, outflow_variable, inflow_param_indices,
                                inflow_source_variables, inflow_passing_variables, newVariableToCopy_path, passing_units,
                                passingStruVariableToSupportingObj_path);
                        // Update the passing variable set.
                        updatePassingVariableSet(outflow_variable, inflow_passing_variables, passing_variables, source_variables_path,
                                newVariableToCopy_path, callee_name);
                        passing_units.add(unit);
                        continue;
                    }
                    int flag_parser = containParserInflowParam(ie, inflow_param_indices);
                    if(needGenerateNewBaseUnit(assignStmt, flag_parser, callee_name)){
                        if(callee.isAbstract()){
                            // Confirm the implemented method when the callee is abstract.
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            callee = getImplementedMethodOfAbstractMethod(analysis_data, ie, base_unit);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                        }
                        BU new_base_unit = generateNewBaseUnit(base_unit, callee, unit, element_type, ie, analysis_data, generated_BU_sigs, null,
                                inflow_param_indices, identifier_variables_path, null_variables_path, numericVariableToValue_path,
                                passingMapVariableToInflowItem_path, passingStruVariableToSupportingObj_path,
                                stringVariableToElementType_path, variableToField_path);
                        if(new_base_unit!=null){
                            base_units.offer(new_base_unit);
                        }
                    }
                    if(isAttrOfPassingVar(callee_name)){
                        flag_attribute = 1;
                    }
                } else {
                    // The inflow variable is the base of an invoking.
                    if (base != null) {
                        if (inflow_source_variables.contains(base) || inflow_passing_variables.contains(base)) {
                            Log.logData(analysis_data, "--- Inflow base.");
                            if(canSkipForInflowBase(base, callee_name)){
                                Log.logData(analysis_data, "--- Can skip, pass.");
                                continue;
                            }
                            // interfaceinvoke $r10.<java.util.List: java.lang.Object[] toArray(java.lang.Object[])>(r12)
                            if(assignStmt == 0 && callee_name.equals("toArray") && (!ie.getArgs().isEmpty())) {
                                Value outflow_variable = ie.getArg(0);
                                // Update the duplication variable info.
                                updatePassingStructuralVariableInfo(null, base_unit, ie, callee_name, outflow_variable, inflow_param_indices,
                                        inflow_source_variables, inflow_passing_variables, newVariableToCopy_path,
                                        passing_units, passingStruVariableToSupportingObj_path);
                                // Update the passing variable set.
                                updatePassingVariableSet(outflow_variable, inflow_passing_variables, passing_variables, source_variables_path,
                                        newVariableToCopy_path, callee_name);
                                passing_units.add(unit);
                                continue;
                            }
                            if(isAttrOfPassingVar(base, callee_name)){
                                flag_attribute = 1;
                            }
                        }
                    }
                }

                // Passing variable.
                if (assignStmt == 1) {
                    AssignStmt as = (AssignStmt) unit;
                    // There is a copy of source variables.
                    if(Utils.hasCopyOfVars(as, source_variables_path)){
                        Log.logData(analysis_data, "--- Copy the source variable." + "\n--- Update the source variable set: " +
                                source_variables);
                        continue;
                    }
                    if (ie == null) {
                        String right_op = as.getRightOp().toString();
                        if (right_op.startsWith("lengthof")) {
                            Log.logData(analysis_data, "--- Get length, pass.");
                            continue;
                        }
                        if(isAttrOfPassingVar(as)){
                            flag_attribute = 1;
                        }
                    }
                    Value outflow_variable = as.getLeftOp();
                    // The obtained data structures are attributions of ParsingPackage.
                    // Therefore, when the outflow variable is ParsingPackage object, we store it and no longer trace it.
                    if(outflow_variable.getType().toString().endsWith("ParsingPackage")){
                        for(Value passing_variable : inflow_passing_variables){
                            removeVariable(passing_variable, passing_variables, newVariableToCopy_path);
                        }

                        Log.logData(analysis_data, "+ Save information -- ParsingPackage object.");
                        saveDataStructureAndRelatedInfo(base_unit, element_type, outflow_variable, return_variable, identifier_variables_path,
                                passingMapVariableToInflowItem_path, passingStruVariableToSupportingObj_path, variableToField_path);
                        Log.logData(analysis_data, "--- Update the passing variable set: " + passing_variables);
                        continue;
                    }
                    // Update the identifier info.
                    updateIdentifierRelatedVariable(as, base_method_name, analysis_data, identifier_variables_path);
                    // Update the Map-type value information.
                    updatePassingMapVariableInfo(as, ie, analysis_data, callee_name, outflow_variable, identifier_variables_path, inflow_param_indices,
                            passing_units, newVariableToCopy_path, passingMapVariableToInflowItem_path);
                    // Update the structural variable info.
                    updatePassingStructuralVariableInfo(as, base_unit, ie, callee_name, outflow_variable, inflow_param_indices,
                            inflow_source_variables, inflow_passing_variables, newVariableToCopy_path, passing_units,
                            passingStruVariableToSupportingObj_path);
                    // Update the passing variable set.
                    if(flag_attribute == 1 || outflow_variable.getType() instanceof BooleanType){
                        addVariable(outflow_variable, passing_variables, newVariableToCopy_path);
                        Log.logData(analysis_data, "--- Update the passing variable set: " + passing_variables);
                    } else {
                        updatePassingVariableSet(outflow_variable, inflow_passing_variables, passing_variables, source_variables_path,
                                newVariableToCopy_path, callee_name);
                    }
                }
                passing_units.add(unit);
            }
        }

        // Save information.
        Log.logData(analysis_data, Utils.generatePartingLine("="));
        Log.logData(analysis_data, "+ Save information -- analyze completely.");
        if(passing_variables.isEmpty()){
            passing_variables.add(null);
        }
        for(Value pv : passing_variables) {
            saveDataStructureAndRelatedInfo(base_unit, element_type, pv, return_variable, identifier_variables_path, passingMapVariableToInflowItem_path,
                    passingStruVariableToSupportingObj_path, variableToField_path);
        }
    }

    public static void findTargetPackageSettings(){
        Log.deleteData(element_data);
        Log.deleteData(method_data);
        Log.deleteData(analysis_data);
        Log.deleteData(target_settings);
        Log.deleteData(package_settings);


        String[] skip_nms = {"\"android\"", "\"array\"", "\"singleInstancePerTask\""};
        String[] skip_mds = {"append", "obtainAttributes", "skipCurrentTag", "unknownTag", "size", "length", "byteSizeOf", "forEachPackage", "recycle"};
        String[] skip_cls = {"android.content.res.XmlResourceParser", "org.xmlpull.v1.XmlPullParser", "android.content.pm.parsing.result.ParseInput",
                "com.android.internal.util.AnnotationValidations", "android.util.Slog"};
        String[] pims = {"parseData"};
        skip_names.addAll(new ArrayList<>(Arrays.asList(skip_nms)));
        skip_methods.addAll(new ArrayList<>(Arrays.asList(skip_mds)));
        skip_classes.addAll(new ArrayList<>(Arrays.asList(skip_cls)));
        //flow_insensitive_methods.addAll(new ArrayList<>(Arrays.asList(pims)));

        findEntryBaseUnits();

        List<BU> analyzed_base_units = new ArrayList<>();

        while (!base_units.isEmpty()) {
            BU base_unit = base_units.poll();
            SootMethod base_method = base_unit.getBaseMethod();

            Log.logData(analysis_data, Utils.generatePartingLine("#"));
            Log.logData(analysis_data, "+ Analyzed method: " + base_method);

            int flag_analyzed = 0;
            String base_unit_sig = generateSignatureOfBaseUnit(base_unit);
            Log.logData(analysis_data, "+ Base-unit sig: " + base_unit_sig.split("&")[1]);
            for(BU abu : analyzed_base_units){
                String abu_sig = generateSignatureOfBaseUnit(abu);
                if(abu_sig.equals(base_unit_sig)){ // Same signature. Multiple methods may invoke the same methods.
                    Log.logData(analysis_data, "--- This method has been analyzed.");
                    flag_analyzed = 1; // This base method has been analyzed.
                    base_unit.setParameters(abu.getParameters()); // The same base units have the same parameters.
                    base_unit.setStartUnit(abu.getStartUnit()); // The same base units have the same start unit.
                    base_unit.setSourceDefs(abu.getSourceDefs()); // The same base units have the same source definitions.
                    List<Pair<String, String>> e_ds = abu.getAssociatedElementTypesAndDataStructures();
                    base_unit.setAssociatedElementTypesAndDataStructures(e_ds); // The same base units have the same <element, structure>.
                    Set<BU> passing_children = abu.getPassingChildren();
                    base_unit.setPassingChildren(passing_children); // The same base units have the same passing callee.
                    if(passing_children != null) {
                        List<BU> parents = Utils.deepCopy(base_unit.getParents()); // Analyzed base unit and this base unit have different parents.
                        parents.add(base_unit);
                        for (BU child : passing_children) {
                            BU new_base_unit = new BU(child.getBaseMethod(), child.getAssociatedElementType(), child.getCallUnit(), parents, null,
                                    child.getIdentifierParamIndices(), child.getInflowParamIndices(), child.getNullParamIndices(), child.getInflowMapParamIndies(),
                                    child.getInflowStruParamIndies(), child.getElementTypeParamIndies(), child.getFieldParamIndies(),
                                    child.getNumericParamIndies());
                            base_units.offer(new_base_unit); // Record the passing base-units.
                        }
                    }
                    break;
                }
            }

            if(flag_analyzed==1) {
                analyzed_base_units.add(base_unit);
                continue;
            }

            analyzed_base_units.add(base_unit);
            // Start analyzing.
            dataFlowAnalysisForBaseUnit(base_unit);

            //Utils.pause();
            //sleep(2000);
        }
        Utils.printPartingLine("#");
        for(Map.Entry<String, Set<String>> entry: associatedElementTypeToDataStructures.entrySet()){
            String associated_element_type = entry.getKey();
            Set<String> data_structures = transferDSSetIfHaveUnknownMapItem(entry.getValue(), analyzed_base_units);
            Log.logData(element_data, Utils.generatePartingLine("#"));
            Log.logData(element_data, "+ Associated element: " + associated_element_type);
            String out = associated_element_type +",";
            for(String ds : data_structures){
                Log.logData(element_data, Utils.generatePartingLine("="));
                Log.logData(element_data, "-- Data structure: " + ds);
                out += ds + ",";
                if(ds!=null && ds.contains("<") && ds.contains(parsedPackage_settings_class)){
                    Log.logData(package_settings, ds + "=>" + associated_element_type);
                }
                if(isTargetPackageSetting(ds)){
                    Log.logData(target_settings, ds + "=>" + associated_element_type);
                    for (BU abu : analyzed_base_units) {
                        List<Pair<String, String>> e_ds = abu.getAssociatedElementTypesAndDataStructures();
                        for (Pair<String, String> e_d : e_ds) {
                            if (associated_element_type.equals(e_d.getO1()) && ds.equals(e_d.getO2())) {
                                Log.logData(element_data, Utils.generatePartingLine("-"));
                                Log.logData(element_data, "--- Call path:");
                                for (BU parent : abu.getParents()) {
                                    Log.logData(element_data, "--- " + parent.getBaseMethod().getSignature());
                                }
                                Log.logData(element_data, "---" + abu.getBaseMethod().getSignature());
                            }
                            break;
                        }
                    }
                }
            }
            System.out.println(out);
        }
    }
}
