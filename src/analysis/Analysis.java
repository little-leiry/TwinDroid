package analysis;

import comparator.VBComparator;
import graph.Graph;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.ConditionExprBox;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.scalar.Pair;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.util.*;

import static java.lang.System.*;

public class Analysis {
    public static String store_base_path = "android12/";

    // One abstract class may be implemented by multiple classes.
    public static Map<SootClass, Set<SootClass>> interfaceClassToImplementedClasses = new HashMap<SootClass, Set<SootClass>>();
    public static Map<SootClass, Set<SootClass>> interfaceClassToSubInterfaceClasses = new HashMap<SootClass, Set<SootClass>>();
    public static Map<SootClass, Set<SootClass>> abstractClassToDerivedClasses = new HashMap<>();
    public static Map<SootClass, Set<SootClass>> abstractClassToSubAbstractClasses = new HashMap<>();

    // skip_names: important names. These names are unlikely an element name.
    public static List<String> skip_names = new ArrayList<>();

    // skip_methods, skip_classes: important methods / classes. If a statement contains this kind of methods / classes, just skipping this statement.
    public static List<String> skip_methods = new ArrayList<>();
    public static List<String> skip_classes = new ArrayList<>();

    // Our analysis is flow-sensitive and path-sensitive. We analyze each path of a method's block graph.
    // But some methods is unsuitable for flow-sensitive
    // In general, these methods contains many If statements,
    // and will generate lots of redundant paths.
    public static List<String> flow_insensitive_methods = new ArrayList<>();

    public static final List<String> element_types = Arrays.asList("adopt-permissions", "application", "compatible-screens", "eat-comment",
            "feature-group", "instrumentation", "key-sets", "manifest", "original-package", "overlay", "package", "package-verifier",
            "attribution", "permission", "permission-group", "permission-tree", "protected-broadcast", "queries", "restrict-update",
            "supports-screens", "supports-input", "uses-configuration", "uses-feature", "uses-gl-texture", "uses-permission",
            "uses-permission-sdk-23", "uses-permission-sdk-m", "uses-sdk", "uses-split", "profileable");


    // Judge whether the condition is met.
    // Replace the Value with its concrete assignment.
    // Sort the list according to the Value name's length first in case that one value name is the prefix of another Value name.
    public static int isConditionMet(IfStmt is, Set<Value> identifier_variables, Set<Value> null_variables,
                                     Map<Value, String> numericVariableToValue){
        String condition = is.getCondition().toString();
        //Log.logData(AnalysisForParsingClass2.analysis_data, "--- If condition: " + condition);
        //Log.logData(AnalysisForParsingClass2.analysis_data, "--- Numeric variable set: " + numericVariableToValue);
        List<ValueBox> vbs = is.getUseBoxes();
        Collections.sort(vbs, new VBComparator());
        int flag_compute = 1;
        for(ValueBox vb : vbs){
            if( vb instanceof ConditionExprBox) continue;
            Value v = vb.getValue();
            if(v instanceof IntConstant) continue;
            if(v instanceof NullConstant) continue;
            if("int_byte_boolean".contains(v.getType().toString())){
                String assign = numericVariableToValue.get(v);
                if(assign==null) {
                    flag_compute = 0;
                    break;
                } else {
                    condition = condition.replace(v.toString(), assign);
                }
            } else if(identifier_variables.contains(v)){ // if(fi.name==null), identifier must not be null.
                condition = condition.replace(v.toString(), "1");
            } else if (null_variables.contains(v)) {
                condition = condition.replace(v.toString(), "null"); // if(r4 == null)
            } else {
                flag_compute = 0;
            }
        }
        if (flag_compute == 1) {
            //Log.logData(AnalysisForParsingClass2.analysis_data, "If condition: " + condition);
            ScriptEngineManager sem = new ScriptEngineManager();
            ScriptEngine se = sem.getEngineByName("js");
            try {
                boolean result = (boolean) se.eval(condition);
                return result? 1:0;
            } catch (ScriptException e) {
                Utils.generatePartingLine("!");
                System.out.println("Computing Error: " + condition);
                System.out.println(is);
                Utils.generatePartingLine("!");
                throw new RuntimeException(e);
            }
        } else { // Cannot compute due to the lack of concrete assignments.
            return -1;
        }
    }

    public static boolean isIdentifierRelatedAssignStmt(AssignStmt as, String base_method_name){
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(ie == null){
            // $r10 = $r6.<android.content.pm.parsing.component.ParsedProcess: java.lang.String name>
            // name or process or tag
            if(Utils.isFieldVariable(as.getRightOp())){
                String[] infos = as.getRightOp().toString().split(" ");
                if(infos[1].endsWith("String") &&
                        (infos[2].endsWith("name>") || infos[2].endsWith("process>") || infos[2].endsWith("tag>"))){
                    return true;
                }
            }
        } else {
            Value base = Utils.getBaseOfInvokeExpr(ie);
            String method_name = ie.getMethod().getName();
            Type return_type = ie.getMethod().getReturnType();
            // $r7 = interfaceinvoke $r3.<android.content.res.XmlResourceParser: java.lang.String getName()>()
            if(base!=null && method_name.startsWith("get") &&
                    return_type != null && return_type.toString().endsWith("String")){
                // name or process or tag
                if("getName_getTag_getProcess".contains(method_name)){
                    return true;
                } else if(method_name.endsWith("Name")){
                    // $r7 = virtualinvoke $r0.<android.content.pm.parsing.component.ParsedActivity: java.lang.String getClassName()>();
                    // getClassName:
                    // $r1 = virtualinvoke r0.<android.content.pm.parsing.component.ParsedMainComponent: java.lang.String getName()>();
                    // return $r1;
                    Body body = ie.getMethod().retrieveActiveBody();
                    Value return_variable = Utils.getReturnVariable(body);
                    if(isIdentifierVariable(base_method_name, body, return_variable, null)){
                        return true;
                    }
                } else {
                    // $r10 = virtualinvoke $r8.<android.content.res.TypedArray: java.lang.String getNonConfigurationString(int,int)>(0, 0);
                    if(base.getType().toString().endsWith("TypedArray") && !ie.getArgs().isEmpty()){
                        // tag
                        if(base_method_name!=null && base_method_name.equals("parseAttribution")){
                            if(ie.getArg(0).toString().equals("1")){
                                return true;
                            }
                        } else { // name or process
                            if (ie.getArg(0).toString().equals("0")) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    public static boolean isIdentifierVariable(String base_method_name, Body body, Value v, Unit end_unit){
        if(body == null || v == null) return false;

        if(!Utils.isStringVariable(v)) return false;

        int flag = 0;
        for (Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                if(as.getLeftOp().equals(v)){
                    if(isIdentifierRelatedAssignStmt(as, base_method_name)){
                        flag = 1;
                    } else { // The variable is redefined.
                        flag = 0;
                    }
                }
                if(unit.equals(end_unit)){
                    break;
                }
            }
        }
        if(flag == 1){
            return true;
        } else {
            return false;
        }
    }

    public static boolean isLeftVarOfAssignStmt(AssignStmt as, Value v){
        if(as==null || v == null) return false;

        v = Utils.getBaseVariable(v); // Variable pre-processing. The whole variable has been redefined.
        if(as.getLeftOp().equals(v)) return true;
        return false;
    }

    public static Value hasLeftVarOfAssignStmt(AssignStmt as, List<Value> vars){
        if(as==null || vars==null) return null;
        for(Value v : vars){
            if(isLeftVarOfAssignStmt(as, v)) {
                return v;
            }
        }
        return null;
    }

    // Judge whether a variable:
    // 1) is one of the assignment's use values and
    // 2) this value appears in the right of the assignment.
    public static boolean isRightVarOfAssignStmt(AssignStmt as, BU base_unit, String log_file, Value v) {
        if(as == null || v == null) return false;

        // Variable pre-processing.
        v = Utils.getArrayVariable(v); // r1[i3] => r1
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(ie!=null) {
            v = getBaseVariableForField(base_unit, log_file, v); // r1.<name> => r1 (r1 only has one field).
        }
        List<ValueBox> vbs = as.getUseBoxes();
        for (ValueBox vb : vbs) {
            Value use_value = vb.getValue();
            if (use_value.equals(v) &&
                    as.getRightOp().toString().contains(v.toString())) {
                return true;
            }
        }
        return false;
    }

    public static List<Value> hasRightVarsOfAssignStmt(AssignStmt as, BU base_unit, String log_file, List<Value> vars) {
        List<Value> result = new ArrayList<>();
        if(as == null || vars == null) return result;
        for(Value v : vars){
            if(isRightVarOfAssignStmt(as, base_unit, log_file, v)){
                result.add(v);
            }
        }
        return result;
    }

    // staticinvoke <android.content.pm.PackageParser: android.util.Pair parsePackageSplitNames(org.xmlpull.v1.XmlPullParser,android.util.AttributeSet)>($r4, $r4)
    // One variable may correspond to multiple parameters.
    public static Set<Integer> isParamOfInvokeExpr(BU base_unit, InvokeExpr ie, String log_file, Value v) {
        Set<Integer> indices = new HashSet<>();
        if(ie == null || v == null) return indices;
        // Variable pre-processing.
        v = Utils.getArrayVariable(v); // r1[0] => r1
        v = getBaseVariableForField(base_unit, log_file, v); // r1.<name> => r1
        List<Value> parameters = ie.getArgs();
        if(parameters.contains(v)) {
            for (int index = 0; index < parameters.size(); index++) {
                if (parameters.get(index).equals(v)) {
                    indices.add(index);
                }
            }
        }
        return indices;
    }

    public static List<Value> hasParamsOfInvokeExpr(BU base_unit, InvokeExpr i, String log_file, List<Value> vars) {
        List<Value> result = new ArrayList<>();
        if(i == null || vars == null) return result;
        for(Value v : vars){
            if(!isParamOfInvokeExpr(base_unit, i, log_file, v).isEmpty()) {
                result.add(v);
            }
        }
        return result;
    }

    public static boolean isWrongPathForIfStmt(List<Block> blocks, List<Integer> block_ids, int block_ids_index, IfStmt is,
                                               Set<Value> identifier_variables, Set<Value> null_variables,
                                               Map<Value, String> numericVariableToValue) {
        int result = isConditionMet(is, identifier_variables, null_variables, numericVariableToValue);
        //Log.logData(AnalysisForParsingClass2.analysis_data, "--- If condition result: " + result);
        if(result != -1 ){
            Unit target_unit = is.getTarget();
            if(target_unit==null){
                String msg = "Cannot find the target Unit of the IfStmt: " + is;
                Utils.terminate(msg);
            }
            if(block_ids_index + 1 <block_ids.size()) {
                if (result == 1) {
                    // When the condition is met, if the next block's first Unit is not the target Unit, this path is incorrect.
                    if (!blocks.get(block_ids.get(block_ids_index + 1)).getHead().equals(target_unit)) {
                        return true;
                    }
                } else {
                    // When the condition is not met, if the next block's first Unit is the target Unit, this path is incorrect.
                    if (blocks.get(block_ids.get(block_ids_index + 1)).getHead().equals(target_unit)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    public static boolean isWrongPathForSwitchStmt(String log_file, List<Block> blocks, List<Integer> block_ids, int block_ids_index,
                                                   LookupSwitchStmt lss, Value case_value, Map<Value, String> numericValueToConcreteAssignment) {
        if(numericValueToConcreteAssignment.containsKey(case_value)){
            String case_id = numericValueToConcreteAssignment.get(case_value); // Find the case id associated with this path.
            if (case_id != null) {
                int id = Integer.parseInt(case_id);
                Unit target_unit;
                if (id != -1) {
                    target_unit = lss.getTarget(id);
                } else {
                    target_unit = lss.getDefaultTarget();
                }
                if (target_unit != null) {
                    if (block_ids_index + 1 < block_ids.size()) {
                        Unit next_block_head = blocks.get(block_ids.get(block_ids_index + 1)).getHead();
                        String msg = "+ Case value: " + case_value + " => " + case_id + "\n+ Target unit (hash code): " + target_unit.hashCode() +
                                "\n+ Next block head (hash code): " + next_block_head.hashCode();
                        Utils.logMsg(log_file, msg, "+");
                        // If the next block's first Unit is not the target Unit, this path is incorrect.
                        if (!next_block_head.equals(target_unit)) {
                            return true;
                        }
                    }
                } else {
                    String msg = "Cannot find the target Unit of the case ID [ " + case_id + " ]." + "\nSwitchStmt: " + lss;
                    Utils.terminate(msg);
                }
            } else { // Cannot confirm the concrete value of case value.
                return false;
            }
        }else {
            String msg = "Cannot find the corresponding case ID of the case value [ " + case_value + " ].";
            Utils.terminate(msg);
        }
        return false;
    }

    public static Value hasRedefinedVariable(AssignStmt as, InvokeExpr ie, List<Value> variables, Unit last_passing_unit,
                                             Set<AssignStmt> source_defs, Map<Value, String> variableToField){

        Value v = hasLeftVarOfAssignStmt(as, variables);
        if (v != null) {
            if(source_defs!=null && source_defs.contains(as))
                return null;

            if (last_passing_unit != null && as.toString().equals(last_passing_unit.toString()))
                return null;


            if (ie != null && ie.getMethod().getDeclaringClass().toString().equals("android.content.pm.parsing.result.ParseInput"))
                return null;

            if(v.getType().toString().equals("boolean")){
                if(as.getUseBoxes().size()==1 && (as.getRightOp() instanceof IntConstant)){ // Assign 0 or 1 to this boolean value directly.
                    return null;
                }
            }
            // For the tainted value related to a field,
            // when it is passed in a method as a parameter,
            // this value may be reassigned this field first.
            String field = Utils.getFieldNameFromAssignStmt(as);
            if(field!=null && variableToField.containsKey(as.getLeftOp())){
                if(variableToField.get(as.getLeftOp()).equals(field)){
                    return null;
                }
            }
            return v;
        }
        return null;
    }

    public static void addVariable(Value variable, List<Value> variables, Map<Value, Value> newVariableToCopy){
        if(variables.contains(variable)) return;
        variable = Utils.getArrayVariable(variable); // r1[i0] => r1
        variables.add(variable);
        Value copy = newVariableToCopy.get(variable);
        if(copy!=null){
            variables.add(copy);
        }
    }

    public static int canStartAnalysis(int flag_analysis, Unit start_unit, int path_sensitive, Unit unit, Set<AssignStmt> source_defs){
        if(flag_analysis == 1) return 1;
        // For the flow-insensitive situation.
        // If the base unit sets a start statement,
        // the analysis should start from this start statement.
        if(path_sensitive == 0) {
            if(start_unit == null) {
                String msg = "Null start unit for flow-insensitive analysis.";
                Utils.terminate(msg);
            }
            if (start_unit.equals(unit)) {
                return 1;
            }
        } else { // For the path sensitive situation.
            // If there are source variable's definition statements,
            // the analysis should start from the first definition statement.
            if(source_defs == null) return 1;

            if (unit instanceof AssignStmt) {
                if (source_defs.contains(((AssignStmt) unit))) {
                    return 1;
                }
            }
        }
        return 0;
    }

    public static void clearCommonDataSet(){
        skip_classes.clear();
        skip_methods.clear();
        flow_insensitive_methods.clear();
    }

    // 0 - flow-insensitive analysis.
    // 1 - path-sensitive analysis, start analyzing from the head block.
    // 2 - path-sensitive analysis, start analyzing from the LCA block.
    // For the method in flow_insensitive_methods, the analysis model = 0;
    // For other methods, if generating path from the head block does not trigger path explosion, the analysis model = 1;
    // Else, if generating path from the LCA block does not trigger path explosion, the analysis model = 2;
    // Else, the analysis model = 0;
    public static int confirmAnalysisModel(String base_method_name, CompleteBlockGraph cbg, List<Block> noteworthy_blocks){
        if (!flow_insensitive_methods.contains(base_method_name)) {
            try {
                if (cbg.getHeads().size() != 1) {
                    String msg = "Special method, has multiple head blocks: " + cbg.getBody().getMethod().getSignature();
                    Utils.terminate(msg);
                }
                Graph.generatePathsFromBlock(cbg.getHeads().get(0));
                System.out.println("+ Currently generated path num: " + Graph.path_num);
                return 1; // Start analyzing from the head block.
            } catch (Exception e) {
                // Reset the data.
                Graph.paths.clear();
                Graph.path.clear();
                Graph.path_num = 0;
                out.println("+ Analysis mode 1: " + e);
            }
            int lca_block_id = Graph.getLeastCommonAncestorOfBlocks(noteworthy_blocks);
            /*int lca_block_id2 = Graph.getLeastCommonAncestorOfBlocksSmart(noteworthy_blocks);
            if (lca_block_id2 != lca_block_id) {
                String msg = "--- Stupid: " + lca_block_id + "\n--- smart: " + lca_block_id2;
                Utils.terminate(msg);
            }*/
            out.println("+ LCA block id: " + lca_block_id);
            try {
                Graph.generatePathsFromBlock(cbg.getBlocks().get(lca_block_id));
                System.out.println("+ Currently generated path num: " + Graph.path_num);
                return 2; // Start analyzing from the LCA block.
            } catch (Exception e) {
                // Reset the data.
                Graph.paths.clear();
                Graph.path.clear();
                Graph.path_num = 0;
                out.println("+ Analysis mode 2: " + e);
            }
        }
        return 0; // flow-insensitive analysis.
    }

    public static SootClass confirmImplementedClass(BU base_unit, Value interface_obj, String log_file, Set<SootClass> class_set){
        Log.logData(log_file, "Multiple implemented classes, try to confirm the concrete one ... ");
        //System.out.println("### " + interface_obj);
        if (interface_obj != null && base_unit != null) {
            // Find the creation of the interface obj to confirm the implemented class.
            Pair<Pair<BU, Value>, Unit> belonging_bu_info = findBelongingBUOfVariable(base_unit, interface_obj);
            BU belonging_bu = belonging_bu_info.getO1().getO1();
            Value corresponding_var = belonging_bu_info.getO1().getO2();
            //System.out.println("=== belonging bu: " + belonging_bu.getBaseMethod());
            //System.out.println("=== Corresponding var: " + corresponding_var);
            if(belonging_bu != null) {
                SootClass implemented_cls = findCreationOfClassObject(belonging_bu.getBaseMethod().retrieveActiveBody(), corresponding_var);
                if (implemented_cls != null && class_set.contains(implemented_cls)) {
                    Log.logData(log_file, "Confirmed!");
                    return implemented_cls;
                }
            }
            SootClass declaring_cls = ((RefType) corresponding_var.getType()).getSootClass();
            if (class_set.contains(declaring_cls)) {
                Log.logData(log_file, "Cannot confirm, choose the farthest ancestor's corresponding variable's declaring class");
                return declaring_cls;
            }
        }
        return null;
    }

    public static String confirmBelongingClsOfField(BU base_unit, Value field_var){
        if(base_unit == null || field_var == null) return null;

        SootClass base_cls = base_unit.getBaseMethod().getDeclaringClass();
        if(Utils.isFieldOfClass(field_var, base_cls)){ // This field belongs to this base-method's declaring class.
            Unit call_unit = base_unit.getCallUnit();
            Value base = Utils.getBaseOfInvokeExpr(Utils.getInvokeOfUnit(call_unit));
            if(base!=null && base.getType() instanceof RefType){
                SootClass call_cls = ((RefType) base.getType()).getSootClass();
                if(!call_cls.equals(base_cls) && call_cls.getSuperclass().equals(base_cls)) {
                    return call_cls.toString();
                }
            }
        } else {
            if(!field_var.getUseBoxes().isEmpty()){
                Value base = field_var.getUseBoxes().get(0).getValue();
                if(base.getType() instanceof RefType){
                    String declaring_cls1 = ((RefType) base.getType()).getSootClass().toString();
                    String declaring_cls2 = field_var.toString().split("<")[1].split(":")[0];
                    if(!declaring_cls1.equals(declaring_cls2)) {
                        return declaring_cls1;
                    }
                }
            }
        }
        return null;
    }

    public static SootMethod confirmImplementedMethod(SootClass implement_class, SootMethod abstract_method){
        for (SootMethod method : implement_class.getMethods()) {
            if (method.isConcrete()) {
                if (method.getSubSignature().equals(abstract_method.getSubSignature())) {
                    if (method.getDeclaration().contains(" volatile ")) { // The return types of the abstract method and its implemented method are different.
                        Body body = method.retrieveActiveBody();
                        for (Unit unit : body.getUnits()) {
                            InvokeExpr i = Utils.getInvokeOfUnit(unit);
                            if (i instanceof VirtualInvokeExpr) {
                                SootMethod implemented_method = i.getMethod();
                                if (implemented_method.getName().equals(abstract_method.getName()) &&
                                        implemented_method.getParameterTypes().equals(abstract_method.getParameterTypes())) { // The actually implemented method.
                                    //System.out.println("--- implemented method: " + implemented_method.getSignature());
                                    return implemented_method;
                                }
                            }
                        }
                    }
                    return method;
                }
            }
        }
        return null;
    }

    public static String confirmInflowItemOfPassingMapVariable(String method_name, InvokeExpr ie, Set<Integer> inflow_param_indices, Set<Value> identifier_variables,
                                                               Map<Value, String> passingMapVariableToInflowItem){
        if(method_name == null || inflow_param_indices == null || inflow_param_indices.isEmpty()) {
            return null;
        }
        String item = "_map";
        // For putAll(map), addAll(map)
        if(method_name.endsWith("All")){
            Value bridge = ie.getArg(0);
            if(passingMapVariableToInflowItem.containsKey(bridge)){
                item = passingMapVariableToInflowItem.get(bridge);
            } else {
                item += "_null";
            }
            return item;
        }
        // For put(key, value), add(map, key, value)
        int flag_key = 0;
        int flag_value = 0;
        if(method_name.equals("add")){
            if(inflow_param_indices.contains(1)){
                flag_key = 1;
            }
            if(inflow_param_indices.contains(2)){
                flag_value = 1;
            }
        } else if(method_name.equals("put")){
            if(inflow_param_indices.contains(0)){
                flag_key = 1;
            }
            if(inflow_param_indices.contains(1)){
                flag_value = 1;
            }
        }
        if(flag_key == 1) {
            Value key = method_name.equals("put")? ie.getArg(0) : ie.getArg(1);
            if(identifier_variables.contains(key)){
                item += "_key(identifier)";
            }else {
                item += "_key";
            }
        }
        if(flag_value == 1){
            item += "_value";
        }
        return item;
    }

    public static String confirmUnknownInflowMapItem(String ds, List<BU> analyzed_base_units){
        String method_sig = ds.split("unknown\\(")[1].split(">")[0] + ">";
        int flag_known = 0;
        for(BU abu : analyzed_base_units){
            if(abu.getBaseMethod().getSignature().equals(method_sig)){
                List<Pair<String, String>> e_ds = abu.getAssociatedElementTypesAndDataStructures();
                if(e_ds == null) {
                    continue;
                }
                List<String> maps = new ArrayList<>();
                for(Pair<String, String> e_d : e_ds) {
                    String struct = e_d.getO2();
                    if(struct != null && struct.contains("_map")){
                        maps.add(struct);
                    }
                }
                if(maps.isEmpty()){
                    continue;
                }
                String bridge = maps.get(0);
                if(!maps.get(0).contains("return")){
                    for(String map : maps){
                        if(map.contains("return")){
                            bridge = map;
                            break;
                        }
                    }
                }
                String inflow_map_item = bridge.split("_map")[1];
                if(inflow_map_item.contains("unknown")){
                    method_sig = inflow_map_item.split("unknown\\(")[1].split(">")[0] + ">";
                    continue;
                }
                ds = ds.split("_unknown")[0] + inflow_map_item;
                flag_known = 1;
            }
            if(flag_known == 1){
                break;
            }
        }
        return ds;
    }

    public static SootClass findCreationOfClassObject(Body body, Value obj){
        Log.logBody(body, store_base_path);
        if(body == null || obj == null) return null;
        // In general, the type of a Jimple object is fixed.
        for(Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                Value left_op = as.getLeftOp();
                Value right_op = as.getRightOp();
                if(left_op.equals(obj)){ // The definition of the object.
                    InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                    if(Utils.isNewStmt(as)){ // The creation of this object.
                        return ((RefType) left_op.getType()).getSootClass();
                    } else if (right_op.getUseBoxes().isEmpty()){ // r1 = r2;
                        obj = as.getRightOp();
                        return findCreationOfClassObject(body, obj);
                    } else if(ie!=null) {
                        SootMethod method = ie.getMethod();
                        if (method.isConcrete()) {
                            body = method.retrieveActiveBody();
                            obj = Utils.getReturnVariable(body);
                            return findCreationOfClassObject(body, obj);
                        }
                    }
                }
            }
        }
        return  null;
    }

    public static Pair<Pair<BU, Value>, Unit> findBelongingBUOfVariable(BU base_unit, Value v){
        if(base_unit == null || v == null) return null;

        List<BU> base_units = Utils.deepCopy(base_unit.getParents());
        base_units.add(base_unit);
        Value var = v;
        Unit call_unit = null;
        for (int i = base_units.size(); i > 0; i--) {
            BU bu = base_units.get(i - 1);
            Map<Value, Integer> parameters = bu.getParameters();
            if(parameters == null){
                String msg = "Cannot find the parameters of the method: " + bu.getBaseMethod();
                Utils.terminate(msg);
            }
            if (parameters.containsKey(var)) { // The variable is a parameter of the method, we need analyze its parent.
                call_unit = bu.getCallUnit(); // The parent's call unit corresponding to this base unit.
                if (i - 1 > 0) {
                    // Transform the variable.
                    Body body = base_units.get(i - 2).getBaseMethod().retrieveActiveBody();
                    for (Unit unit : body.getUnits()) {
                        if (unit.equals(call_unit)) {
                            var = Utils.getInvokeOfUnit(unit).getArg(parameters.get(var));
                            break;
                        }
                    }
                }
            } else { // The variable belongs to this base unit.
                Pair<BU, Value> p1 = new Pair(bu, var);
                Pair<Pair<BU, Value>, Unit> p2 = new Pair<>(p1, call_unit);
                return p2;
            }
        }
        // Cannot find the belonging base unit.
        Pair<BU, Value> p1 = new Pair(null, var);
        Pair<Pair<BU, Value>, Unit> p2 = new Pair<>(p1,call_unit);
        return p2;
    }

    // The return element is related to the current analyze method and its parents.
    public static String getAssociatedElementType(String base_element_type, String element_type){
        if(base_element_type == null){
            return element_type;
        }else if(element_type == null) {
            return base_element_type;
        } else {
            return base_element_type + "_" + element_type;
        }
    }

    // r1.<name> => r1 (r1 only has one field).
    public static Value getBaseVariableForField(BU base_unit, String log_file, Value v){
        if(Utils.isFieldVariable(v)){
            if(v.getUseBoxes().isEmpty()) return v;
            Value base = v.getUseBoxes().get(0).getValue();
            if(base.getType() instanceof RefType) {
                SootClass declaring_cls = ((RefType) base.getType()).getSootClass();
                Set<String> field_names = getFieldNamesOfDeclaringClass(base_unit, declaring_cls, base, log_file);
                if (field_names.size() == 1) {
                    return base;
                }
            }
        }
        return v;
    }

    public static Value getCaseValue(LookupSwitchStmt lss){
        Unit default_unit = lss.getDefaultTarget();
        if (default_unit instanceof GotoStmt) {
            GotoStmt gs = (GotoStmt) default_unit;
            Unit target_unit = gs.getTarget();
            if (target_unit instanceof AssignStmt) {
                AssignStmt as = (AssignStmt) target_unit;
                return as.getLeftOp();
            } else if(target_unit instanceof LookupSwitchStmt){
                LookupSwitchStmt lss_target = (LookupSwitchStmt) target_unit;
                return lss_target.getKey();
            } else if(target_unit instanceof IfStmt){
                return null;
            } else {
                Utils.printPartingLine("!");
                System.out.println("Special default target's target: " + target_unit);
                Utils.printPartingLine("!");
                exit(0);
            }
        } else {
            Utils.printPartingLine("!");
            System.out.println("Special default target (not GotoStmt): " + default_unit);
            Utils.printPartingLine("!");
            exit(0);
        }
        return null;
    }

    public static Set<String> getFieldNamesOfDeclaringClass(BU base_unit, SootClass cls, Value obj, String log_file){
        Set< String> field_names = new HashSet<>();
        if(cls == null) return field_names;
        Set<SootClass> related_classes = new HashSet<>(); // father classes, implemented classes, and implemented class's father classes.
        related_classes.add(cls);
        related_classes.addAll(Utils.getSuperClasses(cls));

        Set<SootClass> related_classes_copy = Utils.deepCopy(related_classes);
        for(SootClass related_cls : related_classes_copy) {
            if (related_cls.isInterface()) { // For interface, find its implemented class.
                SootClass implemented_cls = getImplementedClassOfInterface(base_unit, related_cls, obj, log_file);
                related_classes.add(implemented_cls);
                related_classes.addAll(Utils.getSuperClasses(implemented_cls));
            }
        }
        for(SootClass c : related_classes) {
            for (SootField field : c.getFields()) {
                String field_name = field.getName();
                if(!field_name.equals("CREATOR")) {
                    field_names.add(field.getName());
                }
            }
        }
        return field_names;
    }

    public static Set<Integer> getInflowParamIndices(BU base_unit, InvokeExpr ie, String log_file, List<Value> inflow_passing_variables, List<Value> inflow_source_variables){
        List<Value> inflow_vars = new ArrayList<>(inflow_source_variables);
        inflow_vars.addAll(inflow_passing_variables);
        Set<Integer> inflow_param_indices = new HashSet<>();
        for(Value var : inflow_vars){
            Set<Integer> param_indices = isParamOfInvokeExpr(base_unit, ie, log_file, var);
            inflow_param_indices.addAll(param_indices);
        }
        return inflow_param_indices;
    }

    public static SootMethod getImplementedMethodOfAbstractMethod(String log_file, InvokeExpr ie, BU base_unit){
        if(ie == null) {
            return null;
        }
        SootMethod implemented_method = null;
        if(ie instanceof InterfaceInvokeExpr){ // For interface.
            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
            implemented_method = getImplementedMethodOfAbstractMethodForInterface(log_file, ifi, base_unit);
        } else if (ie instanceof VirtualInvokeExpr){ // For abstract class.
            VirtualInvokeExpr vi = (VirtualInvokeExpr) ie;
            implemented_method = getImplementedMethodOfAbstractMethodForAbstractClass(log_file, vi, base_unit);
        } else {
            String msg = "Special abstract method (special class): " + ie;
            Utils.terminate(msg);
        }
        return implemented_method;
    }

    public static SootMethod getImplementedMethodOfAbstractMethodForAbstractClass(String log_file, VirtualInvokeExpr vi, BU base_unit){
        Value base = vi.getBase();
        SootMethod abstract_method = vi.getMethod();
        SootClass abstract_cls;
        // Get the abstract class.
        if(base!=null) {
            abstract_cls = ((RefType) base.getType()).getSootClass();
        } else {
            abstract_cls = abstract_method.getDeclaringClass();
        }

        Log.logData(log_file, "+ " + vi);
        Log.logData(log_file, "--- Abstract class: " + abstract_cls);
        Log.logData(log_file, "--- Abstract method: " + abstract_method.getSignature());

        // Find the corresponding implemented method.
        Set<SootClass> abstract_class_set = new HashSet<>();
        abstract_class_set.add(abstract_cls);
        SootMethod implemented_method = null;
        while(implemented_method == null) {
            // First, find it from the current abstract class's derived classes.
            SootClass a_cls = abstract_class_set.iterator().next();
            Set<SootClass> derived_classes = abstractClassToDerivedClasses.get(a_cls);
            if (derived_classes == null || derived_classes.size() == 0) {
                String msg = "Special abstract class. Cannot find the derived class of " + a_cls.getName();
                Utils.terminate(msg);
            }
            SootClass implemented_cls;
            if (derived_classes.size() == 1) {
                implemented_cls = derived_classes.iterator().next();
            } else { // If there are multiple derived class, try to confirm the concrete one.
                Log.logData(log_file, Utils.generatePartingLine("~"));
                implemented_cls = confirmImplementedClass(base_unit, base, log_file, derived_classes);
                Log.logData(log_file, Utils.generatePartingLine("~"));
            }
            if (implemented_cls != null) {
                Log.logData(log_file, "--- Implemented class: " + implemented_cls);
                implemented_method = confirmImplementedMethod(implemented_cls, abstract_method);
            } else { // If concrete implemented class cannot be confirmed, analyze the derived classes one by one.
                for (SootClass derived_cls : derived_classes) {
                    implemented_method = confirmImplementedMethod(derived_cls, abstract_method);
                    if (implemented_method != null) {
                        Log.logData(log_file, "--- Implemented class: " + derived_cls);
                        break;
                    }
                }
            }
            if(implemented_method!=null) { // Find the implemented method.
                Log.logData(log_file, "--- Implemented method: " + implemented_method.getSignature());
                return implemented_method;
            }
            // If implemented method cannot be found, analyze this abstract class's sub abstract classes;
            abstract_class_set.remove(a_cls);
            Set<SootClass> sub_abstract_classes = Utils.deepCopy(abstractClassToSubAbstractClasses.get(a_cls));
            if(!sub_abstract_classes.isEmpty()) {
                abstract_class_set.addAll(sub_abstract_classes);
            }
            if(abstract_class_set.isEmpty()) {
                break;
            }
        }
        String msg = "Special abstract method. Cannot find the implemented method of " + abstract_method.getSignature();
        Utils.terminate(msg);
        return null;
    }

    public static SootMethod getImplementedMethodOfAbstractMethodForInterface(String log_file, InterfaceInvokeExpr ifi, BU base_unit){
        Value base = ifi.getBase();
        SootMethod abstract_method = ifi.getMethod();
        SootClass interface_cls;
        // Get the abstract class.
        if(base!=null) {
            interface_cls = ((RefType) base.getType()).getSootClass();
        } else {
            interface_cls = abstract_method.getDeclaringClass();
        }

        Log.logData(log_file, "+ " + ifi);
        Log.logData(log_file, "--- Interface: " + interface_cls);
        Log.logData(log_file, "--- Abstract method: " + abstract_method.getSignature());

        // Find the corresponding implemented class. The implement class must contain the corresponding implemented method.
        // If this interface class does not have its implemented class or implemented method,
        // analyze its sub interface classes;
        Set<SootClass> interface_set = new HashSet<>();
        interface_set.add(interface_cls);
        Set<SootClass> implemented_classes = null;
        while(implemented_classes == null) {
            SootClass i_cls = interface_set.iterator().next();
            implemented_classes = interfaceClassToImplementedClasses.get(i_cls);
            if (implemented_classes != null) { // Has implemented classes.
                break;
            }
            interface_set.remove(i_cls);
            Set<SootClass> sub_interface_classes = Utils.deepCopy(interfaceClassToSubInterfaceClasses.get(interface_cls));
            if(!sub_interface_classes.isEmpty()){
                interface_set.addAll(sub_interface_classes);
            }
            if(interface_set.isEmpty()){
                break;
            }
        }
        if(implemented_classes == null || implemented_classes.size() == 0) {
            String msg = "Special interface. Cannot find the implemented class of " + interface_cls.getName();
            Utils.terminate(msg);
        }

        SootClass implemented_cls;
        if (implemented_classes.size() == 1) {
            implemented_cls = implemented_classes.iterator().next();
        } else { // There are multiple implemented classes, try to confirm the concrete onr.
            Log.logData(log_file, Utils.generatePartingLine("~"));
            implemented_cls = confirmImplementedClass(base_unit, base, log_file, implemented_classes);
            if(implemented_cls==null){ // If cannot confirm, choose the first one.
                implemented_cls = implemented_classes.iterator().next();
                Log.logData(log_file, "Cannot confirm, choose the first.");
            }
            Log.logData(log_file, Utils.generatePartingLine("~"));
        }
        Log.logData(log_file, "--- Implemented class: " + implemented_cls);

        // Find the implemented method.
        while (true) {
            SootMethod implemented_method = confirmImplementedMethod(implemented_cls, abstract_method);
            if(implemented_method!=null){
                Log.logData(log_file, "--- Implemented method: " + implemented_method.getSignature());
                return implemented_method;
            }
            // If this implemented class does not have the implemented method,
            // analyze its parent class.
            implemented_cls = implemented_cls.getSuperclass();
            if (implemented_cls == null) {
                break;
            }
        }

        String msg = "Special abstract method. Cannot find the implemented method of " + abstract_method.getSignature();
        Utils.terminate(msg);
        return null;
    }

    public static SootClass getImplementedClassOfInterface(BU base_unit, SootClass interface_cls, Value interface_obj, String log_file){
        if(interface_cls==null) return null;

        if(interface_obj!=null) {
            // The interface_obj should correspond to interface_cls.
            SootClass cls = ((RefType) interface_obj.getType()).getSootClass();
            if (!interface_cls.equals(cls)) {
                interface_obj = null;
            }
        }

        // Find the corresponding implemented class. The implement class must contain the corresponding implemented method.
        // If this interface class does not have its implemented class or implemented method,
        // analyze its sub interface classes;
        Set<SootClass> interface_set = new HashSet<>();
        interface_set.add(interface_cls);
        Set<SootClass> implemented_classes = null;
        while(implemented_classes == null) {
            SootClass i_cls = interface_set.iterator().next();
            implemented_classes = interfaceClassToImplementedClasses.get(i_cls);
            if (implemented_classes != null) {
                break;
            }
            interface_set.remove(i_cls);
            Set<SootClass> sub_interface_classes = Utils.deepCopy(interfaceClassToSubInterfaceClasses.get(interface_cls));
            if(!sub_interface_classes.isEmpty()){
                interface_set.addAll(sub_interface_classes);
            }
            if(interface_set.isEmpty()){
                break;
            }
        }
        if(implemented_classes == null || implemented_classes.size() == 0) {
            String msg = "Special interface. Cannot find the implemented class of " + interface_cls.getName();
            Utils.terminate(msg);
        }
        // Try to confirm the specific one according to the interface object.
        if(implemented_classes.size() > 1) {
            SootClass implemented_cls = confirmImplementedClass(base_unit, interface_obj, log_file, implemented_classes);
            if (implemented_cls != null && implemented_classes.contains(implemented_cls)) {
                return implemented_cls;
            }
        }
        return implemented_classes.iterator().next();
    }

    public static BU generateNewBaseUnit(BU base_unit, SootMethod callee, Unit call_unit, String element_type, InvokeExpr ie, String log_file, List<String> generated_BU_sigs,
                                         Set<Value> entryBU_variables, Set<Integer> inflow_param_indices, Set<Value> identifier_variables, Set<Value> null_variables,
                                         Map<Value, String> numericVariableToValue, Map<Value, String> passingMapVariableToInflowItem,
                                         Map<Value, Value> passingStruVariableToSupportingObj, Map<Value, String> stringVariableToElementType,
                                         Map<Value, String> variableToField){
        Set<Integer> entryBU_param_indices = new HashSet<>();
        Set<Integer> identifier_param_indices = new HashSet<>();
        Set<Integer> null_param_indices = new HashSet<>();
        Map<Integer, String> inflowMapParamIndexToInflowItem = new HashMap<>();
        Map<Integer, Value> inflowStruParamIndexToSupportingObj = new HashMap<>();
        Map<Integer, String> paramIndexToElementType = new HashMap<>();
        Map<Integer, String> paramIndexToField = new HashMap<>();
        Map<Integer, String> paramIndexToNumericVariable = new HashMap<>();

        generateUsefulParamInfo(ie, inflow_param_indices, entryBU_variables, entryBU_param_indices, identifier_variables, identifier_param_indices,
                null_variables, null_param_indices, numericVariableToValue, paramIndexToNumericVariable, passingMapVariableToInflowItem,
                inflowMapParamIndexToInflowItem, passingStruVariableToSupportingObj, inflowStruParamIndexToSupportingObj,
                stringVariableToElementType, paramIndexToElementType, variableToField, paramIndexToField);
        // Merge the element type for this path and this base-unit.
        String associated_element_type = getAssociatedElementType(base_unit.getAssociatedElementType(), element_type);
        String new_BU_sig = generateSignatureOfNewBaseUnit(callee, associated_element_type, entryBU_param_indices, inflow_param_indices, identifier_param_indices,
                null_param_indices, inflowMapParamIndexToInflowItem, inflowStruParamIndexToSupportingObj, paramIndexToElementType,
                paramIndexToField, paramIndexToNumericVariable);
        if(!generated_BU_sigs.contains(new_BU_sig)) { // This base unit has been generated.
            Log.logData(log_file, "--- Generate a new base unit: " + new_BU_sig);
            generated_BU_sigs.add(new_BU_sig);
            // Store the passing child.
            BU passing_child = new BU(callee, associated_element_type, call_unit, null, entryBU_param_indices, identifier_param_indices, inflow_param_indices,
                    null_param_indices, inflowMapParamIndexToInflowItem, inflowStruParamIndexToSupportingObj, paramIndexToElementType,
                    paramIndexToField, paramIndexToNumericVariable); // This element type only related to the  callee.
            base_unit.storePassingChild(passing_child);
            // Generate a new base unit.
            List<BU> parents = Utils.deepCopy(base_unit.getParents());
            parents.add(base_unit);
            BU new_base_unit= new BU(callee, associated_element_type, call_unit, parents, entryBU_param_indices, identifier_param_indices,
                    inflow_param_indices, null_param_indices, inflowMapParamIndexToInflowItem, inflowStruParamIndexToSupportingObj,
                    paramIndexToElementType, paramIndexToField, paramIndexToNumericVariable);
            return new_base_unit;
        } else {
            Log.logData(log_file, "--- This passing method has been recoded.");
        }
        return null;
    }

    public static String generateSignatureOfBaseUnit(BU base_unit){
        if(base_unit == null) return null;
        SootMethod base_method = base_unit.getBaseMethod();
        String associated_element_type = base_unit.getAssociatedElementType();
        List<Value> source_variables = base_unit.getSourceVariables();
        Set<Integer> entryBU_param_indices = base_unit.getEntryBUParamIndies();
        Set<Integer> inflow_param_indices = base_unit.getInflowParamIndices();
        Set<Integer> identifier_param_indices = base_unit.getIdentifierParamIndices();
        Set<Integer> null_param_indices = base_unit.getNullParamIndices();
        Map<Integer, String> elementType_param_indices = base_unit.getElementTypeParamIndies();
        Map<Integer, String> field_param_indices = base_unit.getFieldParamIndies();
        Map<Integer, String> inflowMap_param_indices = base_unit.getInflowMapParamIndies();
        Map<Integer, Value> inflowStru_param_indices = base_unit.getInflowStruParamIndies();
        Map<Integer, String> numeric_param_indices = base_unit.getNumericParamIndies();

        String sig = base_method.getSignature() + "&" + associated_element_type + "(AET)_" + source_variables + "(SV)_" + entryBU_param_indices + "(EN)_" +
                inflow_param_indices + "(S)_" + identifier_param_indices + "(I)_" + null_param_indices + "(NULL)_" + elementType_param_indices + "(ET)_" +
                field_param_indices + "(F)_" + inflowMap_param_indices + "(MAP)_" + inflowStru_param_indices + "(STRU)_" + numeric_param_indices + "(NUM)";
        return sig;
    }

    public static String generateSignatureOfNewBaseUnit(SootMethod callee, String associated_element_type, Set<Integer> entryBU_param_indices, Set<Integer> inflow_param_indices,
                                                        Set<Integer> identifier_param_indices, Set<Integer> null_param_indices, Map<Integer, String> inflowMapParamIndexToInflowItem,
                                                        Map<Integer, Value> inflowStrucParamIndexToSupportingObject, Map<Integer, String> paramIndexToElementType,
                                                        Map<Integer, String> paramIndexToField, Map<Integer, String> paramIndexToNumericValue){

        String sig = callee.getSignature() + associated_element_type + "(AET)_" + entryBU_param_indices + "(EN)_" + inflow_param_indices + "(S)_" +
                identifier_param_indices + "(I)_" +  null_param_indices + "(NULL)_" + inflowMapParamIndexToInflowItem + "(MAP)_" +
                inflowStrucParamIndexToSupportingObject + "(STRU)_" + paramIndexToElementType + "(ET)_" + paramIndexToField + "(F)_" +
                paramIndexToNumericValue + "(NUM)";

        return sig;

    }

    public static void generateUsefulParamInfo(InvokeExpr ie, Set<Integer> inflow_param_indies, Set<Value> entryBU_variables, Set<Integer> entryBU_param_indices,
                                               Set<Value> identifier_variables, Set<Integer> identifier_param_indices, Set<Value> null_variables,
                                               Set<Integer> null_param_indices, Map<Value, String> numericVariableToValue, Map<Integer, String> paramIndexToNumericValue,
                                               Map<Value, String> passingMapVariableToInflowItem, Map<Integer, String> inflowMapParamIndexToInflowItem,
                                               Map<Value, Value> passingStruVariableToSupportingObj, Map<Integer, Value> inflowStruParamIndexToSupportingObject,
                                               Map<Value, String> stringVariableToElementType, Map<Integer, String> paramIndexToElementType,
                                               Map<Value, String> variableToField, Map<Integer, String> paramIndexToField){
        if(ie == null || inflow_param_indies == null){ // A newly generated base unit.
            return;
        }
        // Keep the passing map variable, duplication item, entry base unit-related variable, and identifier-related variable info.
        for(int inflow_param_index : inflow_param_indies){
            Value inflow_param = ie.getArg(inflow_param_index);
            // Structural-type variable set.
            if(passingStruVariableToSupportingObj != null && Utils.isStructuralVariable(inflow_param)){
                if(passingStruVariableToSupportingObj.containsKey(inflow_param)){
                    inflowStruParamIndexToSupportingObject.put(inflow_param_index, passingStruVariableToSupportingObj.get(inflow_param));
                } else {
                    String msg = "Cannot find the supporting object of the structural object: " + inflow_param;
                    Utils.terminate(msg);
                }
            }
            // Map-type variable set.
            if (passingMapVariableToInflowItem != null && Utils.isMapVariable(inflow_param)) {
                String inflow_map_item = passingMapVariableToInflowItem.get(inflow_param);
                if (inflow_map_item != null) {
                    inflowMapParamIndexToInflowItem.put(inflow_param_index, inflow_map_item);
                } else {
                    String msg = "Cannot find the inflow item of the inflow Map variable: " + inflow_param;
                    Utils.terminate(msg);
                }
            }
            // Entry base-unit-related variable set.
            if(entryBU_variables!=null && entryBU_variables.contains(inflow_param)){
                entryBU_param_indices.add(inflow_param_index);
            }
            // Identifier-related variable set.
            if(identifier_variables!=null && identifier_variables.contains(inflow_param)){
                identifier_param_indices.add(inflow_param_index);
            }
        }
        // Keep the null, numeric, element type-related, and field-related parameter info.
        for(int index = 0; index < ie.getArgs().size(); index++){
            Value param = ie.getArg(index);
            // Null variable set.
            if(null_variables != null && null_variables.contains(param)) { // r1 = null, F(r1)
                null_param_indices.add(index);
            }
            if(param instanceof NullConstant) { // F(null)
                null_param_indices.add(index);
            }
            // Element type-related variable set.
            if(stringVariableToElementType!=null && stringVariableToElementType.containsKey(param)){ // $r1 = "activity", F($r1)
                paramIndexToElementType.put(index, stringVariableToElementType.get(param));
            }
            if(param instanceof StringConstant){ // F("activity")
                if(element_types.contains(param.toString())){
                    paramIndexToElementType.put(index, param.toString());
                }
            }
            // Numeric variable set.
            if (numericVariableToValue != null && numericVariableToValue.containsKey(param)) { // $i1 = 1, F(i1)
                String value = numericVariableToValue.get(param);
                if(value!=null) {
                    paramIndexToNumericValue.put(index, value);
                }
            }
            if(param instanceof IntConstant){ // F(1)
                paramIndexToNumericValue.put(index, param.toString());
            }
            // Field-related variable set.
            if(variableToField!=null && variableToField.containsKey(param)){
                paramIndexToField.put(index, variableToField.get(param));
            }
        }
    }

    public static void initializeInterfaceAndAbstractClassesInfo(){
        for(SootClass cls : Scene.v().getClasses()){
            // Interface info.
            for (SootClass interface_class : cls.getInterfaces()) { // A class can implement multiple interface.
                if(cls.isInterface()){ // interface1 extends interface
                    Set<SootClass> sub_interfaces = interfaceClassToSubInterfaceClasses.get(interface_class);
                    if(sub_interfaces==null){
                        sub_interfaces = new HashSet<>();
                        sub_interfaces.add(cls);
                        interfaceClassToSubInterfaceClasses.put(interface_class, sub_interfaces);
                    } else {
                        sub_interfaces.add(cls);
                    }
                } else { // (abstract) class implements interface
                    Set<SootClass> implemented_classes = interfaceClassToImplementedClasses.get(interface_class);
                    if (implemented_classes == null) {
                        implemented_classes = new HashSet<>();
                        implemented_classes.add(cls);
                        interfaceClassToImplementedClasses.put(interface_class, implemented_classes);
                    } else {
                        implemented_classes.add(cls);
                    }
                }
            }
            // Abstract class info.
            if(cls.hasSuperclass()){ // A class only can extend one class.
                SootClass parent_class = cls.getSuperclass();
                if(parent_class.isAbstract()){
                    Set<SootClass> derived_classes = abstractClassToDerivedClasses.get(parent_class);
                    if(derived_classes == null){
                        derived_classes = new HashSet<>();
                        derived_classes.add(cls);
                        abstractClassToDerivedClasses.put(parent_class, derived_classes);
                    } else {
                        derived_classes.add(cls);
                    }
                    if(cls.isAbstract()){
                        Set<SootClass> sub_abstract_classes = abstractClassToSubAbstractClasses.get(parent_class);
                        if(sub_abstract_classes == null){
                            sub_abstract_classes = new HashSet<>();
                            sub_abstract_classes.add(cls);
                            abstractClassToSubAbstractClasses.put(parent_class, sub_abstract_classes);
                        } else {
                            sub_abstract_classes.add(cls);
                        }
                    }
                }
            }
        }
    }

    public static void initializeUsefulInfo(BU base_unit, Body body, List<Value> source_variables, Set<Value> entryBU_variables, Set<Value> identifier_variables,
                                            Set<Value> null_variables, Map<Value, String> numericVarToValue, Map<Value, String> passingMapVarToInflowItem,
                                            Map<Value, Value> passingStruVarToSupportObj, Map<Value, String> stringVarToElementType,
                                            Map<Value, String> variableToField){
        // Initialize base unit's parameters.
        if(base_unit.getParameters() == null) {
            for (Unit unit : body.getUnits()) {
                if (unit instanceof IdentityStmt) {
                    IdentityStmt is = (IdentityStmt) unit;
                    storeParameterOfBaseUnit(base_unit, is);
                }
            }
        }
        Map<Value, Integer> paramToIndex = base_unit.getParameters();
        // Initialize source variable set, structure variable set, map variable set, entry base unit related variable set, identifier related variable set.
        // These variables are passing variables.
        if(source_variables.isEmpty()) {
            Set<Integer> entryBU_param_indices = base_unit.getEntryBUParamIndies();
            Set<Integer> identifier_param_indices = base_unit.getIdentifierParamIndices();
            Set<Integer> inflow_param_indices = base_unit.getInflowParamIndices();
            Map<Integer, String> inflowMapParamIndexToInflowItem = base_unit.getInflowMapParamIndies();
            Map<Integer, Value> inflowStruParamIndexToSupportingObj = base_unit.getInflowStruParamIndies();
            for (int inflow_param_index : inflow_param_indices) {
                Value inflow_param = Utils.getParamByIndex(paramToIndex, inflow_param_index);
                if (inflow_param != null) {
                    source_variables.add(inflow_param);
                    if(inflowMapParamIndexToInflowItem!=null && inflowMapParamIndexToInflowItem.containsKey(inflow_param_index)){
                        passingMapVarToInflowItem.put(inflow_param, inflowMapParamIndexToInflowItem.get(inflow_param_index));
                    }
                    if(inflowStruParamIndexToSupportingObj!=null && inflowStruParamIndexToSupportingObj.containsKey(inflow_param_index)){
                        passingStruVarToSupportObj.put(inflow_param, inflowStruParamIndexToSupportingObj.get(inflow_param_index));
                    }
                    if(identifier_param_indices!=null && identifier_param_indices.contains(inflow_param_index)){
                        identifier_variables.add(inflow_param);
                    }
                    if(entryBU_variables!=null) {
                        if(entryBU_param_indices!=null && entryBU_param_indices.contains(inflow_param_index)){
                            entryBU_variables.add(inflow_param);
                        }
                    }
                } else {
                    String msg =  "Null inflow parameter." + "\nMethod: " + base_unit.getBaseMethod().getSignature() +
                            "\nInflow parameter index: " + inflow_param_index;
                    Utils.terminate(msg);
                }
            }
        } else { // Only the entry base unit's source variable set is not empty;
            for(Value source_variable : source_variables){
                if(Utils.isMapVariable(source_variable)){
                    passingMapVarToInflowItem.put(source_variable, "_map_value");
                }
                if(entryBU_variables!=null) {
                    entryBU_variables.add(source_variable);
                }
            }
        }
        // Initialize element type related variable set, field related variable set, numeric variable set, null variable set.
        // These variables may not be passing variables.
        Set<Integer> null_param_indices = base_unit.getNullParamIndices();
        Map<Integer, String> paramIndexToElementType = base_unit.getElementTypeParamIndies();
        Map<Integer, String> paramIndexToField = base_unit.getFieldParamIndies();
        Map<Integer, String> paramIndexToNumericValue = base_unit.getNumericParamIndies();
        for(Map.Entry<Value, Integer> entry : paramToIndex.entrySet()){
            Value param = entry.getKey();
            int param_index = entry.getValue();
            if(null_param_indices != null && null_param_indices.contains(param_index)){
                null_variables.add(param);
            }
            if(stringVarToElementType!=null) {
                if(paramIndexToElementType!=null && paramIndexToElementType.containsKey(param_index)){
                    stringVarToElementType.put(param, paramIndexToElementType.get(param_index));
                }
            }
            if(paramIndexToField!=null && paramIndexToField.containsKey(param_index)){
                variableToField.put(param, paramIndexToField.get(param_index));
            }
            if(paramIndexToNumericValue!=null && paramIndexToNumericValue.containsKey(param_index)){
                numericVarToValue.put(param, paramIndexToNumericValue.get(param_index));
            }
        }
    }



    public static void removeVariable(Value variable, List<Value> variables, Map<Value, Value> newVariableToCopy){
        variable = Utils.getArrayVariable(variable); // r1[i0] ==> r1
        int index = variables.indexOf(variable);
        variables.remove(variable);
        // For the situation that the inflow variable is related to a newly constructed object.
        Value copy = newVariableToCopy.get(variable);
        if(copy!=null){
            variables.remove(copy);
        } else if(newVariableToCopy.containsValue(variable) && (index - 1)>0){
            Value v = variables.get(index -1);
            if(newVariableToCopy.containsKey(v)){
                variables.remove(v);
            }
        }
    }

    public static void storePassingMapVariableAndCorrespondingInflowItem(Value passing_map_variable, String inflow_map_item, Map<Value, Value> newVariableToCopy,
                                                                         Map<Value, String> passingMapVariableToInflowItem){
        if(passing_map_variable==null || inflow_map_item == null){
            return;
        }
        // If the passing Map-type variable is a newly constructed object, its copy also needs to be kept.
        passingMapVariableToInflowItem.put(passing_map_variable, inflow_map_item);
        if(newVariableToCopy!=null && newVariableToCopy.containsKey(passing_map_variable)){
            Value copy = newVariableToCopy.get(passing_map_variable);
            if(copy!=null) {
                passingMapVariableToInflowItem.put(copy, inflow_map_item);
            }
        }
    }

    public static void storeNullVariable(AssignStmt as, Set<Value> null_variables, Map<Value, Value> newVariableToCopy){
        if(as == null || null_variables == null) return;
        Value left_op = as.getLeftOp();
        Value right_op = as.getRightOp();
        if(right_op instanceof NullConstant){ // r14 = null;
            null_variables.add(left_op);
            // If the null variable is a newly constructed object, its copy also needs to be kept.
            if(newVariableToCopy!=null && newVariableToCopy.containsKey(left_op)){
                Value copy = newVariableToCopy.get(left_op);
                if(copy!=null) {
                    null_variables.add(copy);
                }
            }
        } else if (Utils.hasCopyOfVars(as, new ArrayList<>(null_variables))) { // r15 = r14, r14 is in the null variable set.
            null_variables.add(left_op);
        } else if (null_variables.contains(left_op)) { // This null variable is redefined.
            null_variables.remove(left_op);
        }
    }

    // Store the byte value's concrete assignment.
    // For the case ID transform of the two associated switch-case statements.
    public static void storeNumericVariableAndCorrespondingValue(AssignStmt as, Map<Value, String> numericVariableToValue){
        Value left_op = as.getLeftOp();
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(!left_op.getUseBoxes().isEmpty()) return;
        List<ValueBox> vbs = as.getUseBoxes();
        if(Utils.isNumericVariable(left_op)){
            if(ie == null && vbs.size() == 1){
                Value right_op = as.getRightOp();
                if(right_op instanceof IntConstant){ // b1 = 2
                    numericVariableToValue.put(left_op, right_op.toString());
                } else {// b1 = b2
                    String assign = numericVariableToValue.get(right_op);
                    numericVariableToValue.put(left_op, assign);
                }
            } else if(ie!=null) { // b1 is the return value of a method.
                numericVariableToValue.put(left_op, null);
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

    public static void storeNewVariableAndCorrespondingCopy(AssignStmt as, Map<Value, Value> newVariableToCopy){
        if(as == null || newVariableToCopy == null) return;

        if(Utils.isNewStmt(as)) { // $r1 = new XXX
            Value new_value = as.getLeftOp();
            newVariableToCopy.put(new_value, null);
        } else if(Utils.hasCopyOfVars(as, new ArrayList<>(newVariableToCopy.keySet()))){
            Value orig = as.getRightOp();
            Value copy = as.getLeftOp();
            if(newVariableToCopy.get(orig) == null){
                newVariableToCopy.put(orig, copy);
            } else if (!newVariableToCopy.get(orig).equals(copy)) {
                String msg = "The new value [ " + orig + " ] already has a copy : " + newVariableToCopy.get(orig) +
                        "\nThe new copy is: " + as;
                Utils.terminate(msg);
            }
        } else if(newVariableToCopy.containsKey(as.getLeftOp())){ // This variable is re-defined.
            newVariableToCopy.remove(as.getLeftOp());
        }
    }

    public static void storeParameterOfBaseUnit(BU base_unit, IdentityStmt is){
        if(base_unit == null || is == null) return;

        int index = Utils.isParamStmt(is);
        if(index!=-1){
            Value param = is.getLeftOp();
            base_unit.storeParameter(param, index);
        }
    }

    public static void storeVariableAndCorrespondingField(AssignStmt as, BU base_unit, Map<Value, String> variableToField){
        String field = Utils.getFieldNameFromAssignStmt(as);
        if(field!=null){ // $r1 = $r6.<android.content.pm.PackageInfo: android.content.pm.ActivityInfo[] activities>
            String cls = confirmBelongingClsOfField(base_unit, as.getRightOp());
            if(cls!=null){
               field += "_" + cls + "(BC)";
            }
            variableToField.put(as.getLeftOp(), field);
        } else if (Utils.hasCopyOfVars(as, new ArrayList<>(variableToField.keySet()))){ // $r2 = $r1, $r1 is in valueToField
            Value copy = as.getLeftOp();
            Value orig = as.getRightOp();
            variableToField.put(copy, variableToField.get(orig));
        } else if(variableToField.containsKey(as.getLeftOp())){ // This value is re-defined.
            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
            if(ie!=null && ie.getArgs().contains(as.getLeftOp())){
                return;
            }
            variableToField.remove(as.getLeftOp());
        }
    }

    public static AssignStmt transferCorrectAssignStmt(AssignStmt as, String log_file, List<Unit> passing_units){
        if(as == null || passing_units.isEmpty()) return null;

        // $r5 = staticinvoke <android.content.pm.parsing.component.ParsedProcessUtils: android.content.pm.parsing.result.ParseResult parseProcesses
        // $r6 = interfaceinvoke $r5.<android.content.pm.parsing.result.ParseResult: java.lang.Object getResult()>()
        // $r7 = (java.util.Map) $r6
        Value bridge_value = as.getUseBoxes().get(1).getValue();
        for (int i = passing_units.size(); i > 0 ; i--) {
            Unit passing_unit = passing_units.get(i - 1);
            if (passing_unit instanceof AssignStmt) {
                AssignStmt passing_as = (AssignStmt) passing_unit;
                if (passing_as.getLeftOp().equals(bridge_value)) {
                    InvokeExpr passing_ie = Utils.getInvokeOfAssignStmt(passing_as);
                    if (passing_ie == null) {
                        continue;
                    }
                    if (passing_ie.getMethod().getName().equals("getResult")) {
                        bridge_value = ((InterfaceInvokeExpr) passing_ie).getBase();
                        continue;
                    }
                    String msg = "Transfer correct invocation: " + passing_as;
                    Utils.logMsg(log_file, msg, "+");
                    return passing_as;
                }
            }
        }
        return null;
    }

    public static Set<String> transferDSSetIfHaveUnknownMapItem(Set<String> data_structures, List<BU> analyzed_base_units){
        Set<String> data_structures_transferred = Utils.deepCopy(data_structures);
        for(String ds : data_structures){
            if(ds!=null && ds.contains("unknown")){
                data_structures_transferred.remove(ds);
                out.println("Before: " + ds);
                ds = confirmUnknownInflowMapItem(ds, analyzed_base_units);
                out.println("After: " + ds);
                data_structures_transferred.add(ds);
            }
        }
        return data_structures_transferred;
    }

    public static void updateIdentifierRelatedVariable(AssignStmt as, String base_method_name, String log_file, Set<Value> identifier_variables){
        if(as == null || base_method_name == null || identifier_variables == null) return;

        int orig_size = identifier_variables.size();
        if(isIdentifierRelatedAssignStmt(as, base_method_name)){
            identifier_variables.add(as.getLeftOp());
        } else if (Utils.hasCopyOfVars(as, new ArrayList<>(identifier_variables))) { // $r1 = $r2, $r2 is in the identifier variable set.
            identifier_variables.add(as.getLeftOp());
        } else if (identifier_variables.contains(as.getLeftOp())){ // This variable is redefined.
            identifier_variables.remove(as.getLeftOp());
        }
        if(identifier_variables.size()!=orig_size) {
            Log.logData(log_file, "--- Update the identifier-related variable set: " + identifier_variables);
        }
    }
    public static void updatePassingMapVariableInfo(AssignStmt as, InvokeExpr ie, String log_file, String method_name, Value outflow_variable,
                                                    Set<Value> identifier_variables, Set<Integer> inflow_param_indices, List<Unit> passing_units,
                                                    Map<Value, Value> newVariableToCopy, Map<Value, String> passingMapVariableToInflowItem){
        if(!Utils.isMapVariable(outflow_variable)) return;

        String inflow_map_item = null;
        if(ie==null) {
            Value right_op = as.getRightOp();
            if (right_op.getUseBoxes().isEmpty()) { // r1 = r2
                inflow_map_item = passingMapVariableToInflowItem.get(right_op);
            } else if (right_op.toString().startsWith("(")) { // In general, this situation involves a method's return value. r1 = (Map) r2
                AssignStmt correct_as = transferCorrectAssignStmt(as, log_file, passing_units); // Find the invocation statement.
                InvokeExpr correct_ie = Utils.getInvokeOfAssignStmt(correct_as);
                if(correct_as == null || correct_ie == null){
                    String msg = "Transfer unsuccessfully, transferred AssignStmt: " + correct_as;
                    Utils.terminate(msg);
                }
                SootMethod correct_callee = correct_ie.getMethod();
                if(correct_callee.getName().equals("get")){ // Map<key,Map<key-value>>
                    Value map_value = Utils.getBaseOfInvokeExpr(correct_ie);
                    if(passingMapVariableToInflowItem.containsKey(map_value)){
                        inflow_map_item = passingMapVariableToInflowItem.get(map_value);
                        if(inflow_map_item.contains("_value")){
                            inflow_map_item = "_map_value";
                        }
                    } else {
                        inflow_map_item = "_map_null";
                    }
                }else {
                    inflow_map_item = "_map_unknown(" + correct_callee.getSignature() + ")";
                }
            }
        } else if("add_addAll_put_putAll".contains(method_name)){
            inflow_map_item = confirmInflowItemOfPassingMapVariable(method_name, ie, inflow_param_indices,
                    identifier_variables, passingMapVariableToInflowItem);
        } else {
            inflow_map_item = "_map_unknown(" + ie.getMethod().getSignature() + ")";
        }
        if(inflow_map_item != null){
            storePassingMapVariableAndCorrespondingInflowItem(outflow_variable, inflow_map_item, newVariableToCopy, passingMapVariableToInflowItem);
        } else{
            String msg = "Cannot confirm the inflow map item: " + as;
            Utils.terminate(msg);
        }
        Log.logData(log_file, "--- Update the Map-type variable info: " + passingMapVariableToInflowItem);
    }
}
