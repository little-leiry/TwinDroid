package analysis;

import graph.Graph;
import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.scalar.Pair;

import java.util.*;

import static java.lang.System.exit;
import static java.lang.System.out;

public class AnalysisForSystemClass2 extends Analysis {
    // The base units needed to be analysed.
    // Each object consists of <base method, source variable set, associated element type>
    // Use queue to do BFS.
    public static Queue<BU> base_units = new LinkedList<>();

    // method => {element type => data structures}.
    public static Map<SootMethod, Map<String, Set<String>>> methodToAETToDSs = new HashMap<SootMethod, Map<String, Set<String>>>();

    //Log files
    public static final String entry_bridges = store_base_path + "logs/processing/entry_bridges.txt";
    public static final String processing_methods_baseInfo = store_base_path + "logs/processing/processing_methods_baseInfo.txt";
    // Analysis.
    public static final String method_data = store_base_path + "logs/processing/method_data.txt";
    public static final String analysis_data = store_base_path + "logs/processing/analysis_data.txt";
    // Results.
    public static final String suspicious_methods = store_base_path + "logs/processing/suspicious_methods.txt";
    public static final String suspicious_method_names = store_base_path + "logs/processing/suspicious_method_names.txt";
    public static final String suspicious_methods_final = store_base_path + "logs/processing/suspicious_methods_final.txt";
    public static final String suspicious_methods_final_names = store_base_path + "logs/processing/suspicious_method_names_final.txt";
    public static final String processing_method_data = store_base_path + "logs/processing/processing_method_data.txt";

    // Element types represent target package settings.
    public static boolean isDeDuplicateTargetSetting(Map<String,Set<String>> AETToDSs_filtered){
        int element_type_size = AETToDSs_filtered.keySet().size();
        for(String element_type : AETToDSs_filtered.keySet()){
            if(element_type.contains("attribution") || element_type.contains("feature") || element_type.contains("uses-permission")){
                element_type_size -= 1;
            }
        }
        if(element_type_size > 0){
            return false;
        } else {
            System.out.println("=== Deduplicate.");
            return true;
        }
    }

    public static boolean isNoteworthyUnit(BU base_unit, Unit unit, List<Value> source_variables, Set<AssignStmt> source_defs){
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
            // Noteworthy unit -- The source variable appears in the right of the Assignment statement.
            if(!hasRightVarsOfAssignStmt(as, base_unit, analysis_data, source_variables).isEmpty()) {
                // Filter some uninteresting types.
                if(Utils.hasCopyOfVars(as, source_variables)){
                    return false;
                }
                if (source_variables.contains(base)) {
                    String method_name = ie.getMethod().getName();
                    if(canSkipForInflowBase(base, method_name)){
                        return false;
                    }
                }
                if (!hasParamsOfInvokeExpr(base_unit, ie, analysis_data, source_variables).isEmpty()) {
                    SootMethod method = ie.getMethod();
                    String method_name = method.getName();
                    if(canSkipForInflowParam(base, method, method_name)){
                        return false;
                    }
                }
                return true;
            }
        } else if (unit instanceof InvokeStmt) {
            InvokeExpr ie = ((InvokeStmt) unit).getInvokeExpr();
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- pass in the source variable as a parameter.
            if (!hasParamsOfInvokeExpr(base_unit, ie, analysis_data, source_variables).isEmpty()) {
                SootMethod method = ie.getMethod();
                String method_name = method.getName();
                if(canSkipForInflowParam(base, method, method_name)){
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

    public static int isAttrOfPassingVar(InvokeExpr ie, String method_name, Set<Value> entryBU_variables, Set<Integer> inflow_param_indices){
        if(method_name.startsWith("get")){
            //System.out.println("=== " + ie);
            if (Utils.getBaseOfInvokeExpr(ie) == null) { // get(..., entryBU_var, ...)
                for(int param_index : inflow_param_indices){
                    Value param = ie.getArg(param_index);
                    if(entryBU_variables.contains(param)){
                        return 2;
                    }
                }
            }
            return 1;
        }
        return -1;
    }
    public static int isAttrOfPassingVar(Value base, String method_name, Set<Value> entryBU_variables){
        if(base != null){
            // $r6 = virtualinvoke r4.<android.content.pm.parsing.component.ParsedProvider: java.lang.String getAuthority()>()
            // $r7 = virtualinvoke $r6.<java.lang.String: java.lang.String[] split(java.lang.String)>(";")
            if(method_name.startsWith("get") || method_name.startsWith("next") ||
                    "split_substring_indexOf_values_keySet_entrySet_iterator".contains(method_name)){
                if(entryBU_variables.contains(base)) {
                    return 2;
                }
                return 1;
            }
        }
        return -1;
    }

    public static int isAttrOfPassingVar(AssignStmt as, Set<Value> entryBU_variables){
        List<ValueBox> vbs = as.getUseBoxes();
        String right_op = as.getRightOp().toString();
        Value likely_attribute = null;
        if (vbs.size() == 1){
            if(Utils.isCopyStmt(as)){
                likely_attribute = as.getRightOp();
            }
        } else if (vbs.size() == 2) {
            // $r4 = interfaceinvoke $r3.<java.util.List: java.lang.Object get(int)>(i1)
            // $r5 = (android.content.pm.parsing.component.ParsedAttribution) $r4
            // $r6 = $r5.<android.content.pm.parsing.component.ParsedAttribution: java.lang.String tag>
            Value use_value = vbs.get(1).getValue();
            if(right_op.contains(".<")){
                likely_attribute = use_value;
            } else if (right_op.startsWith("(")){
                if(use_value.getType().toString().equals("java.lang.Object")){
                    likely_attribute = use_value;
                }
            }
        } else if (vbs.size() == 3){
            // $r6 = $r7[i2]
            if(right_op.contains("[")){
                likely_attribute = vbs.get(1).getValue();
            }
        }
        if(likely_attribute!=null) {
            if (entryBU_variables.contains(likely_attribute)) {
                return 2;
            }
            return 1;
        }
        return -1;
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
        if(method_name.startsWith("remove") || method_name.startsWith("dump") || method_name.startsWith("log") ||
                method_name.startsWith("count")){
            return true;
        }
        if(skip_classes.contains(declaring_class) || skip_methods.contains(method_name)){
            return true;
        }
        if(declaring_class.endsWith("Log") || declaring_class.endsWith("log")){
            return true;
        }
        return false;
    }

    public static boolean canSkipForInflowParam(Value base, SootMethod method, String method_name){
        String declaring_class;
        if (base != null) {
            declaring_class = ((RefType) base.getType()).getSootClass().getName();
        } else {
            declaring_class = method.getDeclaringClass().getName();
        }

        if (skip_methods.contains(method_name) || skip_classes.contains(declaring_class)) {
            return true;
        }
        if(declaring_class.endsWith("Log") || declaring_class.endsWith("log")){
            return true;
        }
        if(declaring_class.contains("ExternalSyntheticLambda")){
            return true;
        }
        if (method_name.startsWith("dump") || method_name.startsWith("log")) {
            return true;
        }
        return false;
    }

    public static String adjustVariableSetIfVariableRedefined(AssignStmt as, BU base_unit, String element_type, InvokeExpr ie, Value return_variable, Set<Value> entryBU_variables,
                                                            Set<AssignStmt> source_defs, List<Unit> passing_units, List<Value> passing_variables,
                                                            List<Value> source_variables, Map<Value, Value> newVariableToCopy,
                                                            Map<Value, String> passingMapVariableToInflowItem,
                                                            Map<Value, String> variableToField){
        Unit last_passing_unit = passing_units.isEmpty()?  null : passing_units.get(passing_units.size() - 1);
        Value redefined_variable = hasRedefinedVariable(as, ie, source_variables, last_passing_unit, source_defs, variableToField);
        if (redefined_variable != null) {
            source_variables.remove(redefined_variable);
            Log.logData(analysis_data, "=");
            String msg = "+ Unit: " + as + "\n--- The source variable [ " + as.getLeftOp() + " ] is re-defined, remove it." +
                    "\n--- Updated the source variable set: " + source_variables;
            Log.logData(analysis_data, msg);
        } else {
            redefined_variable = hasRedefinedVariable(as, ie, passing_variables, last_passing_unit, source_defs, variableToField);
            if (redefined_variable!=null) {
                Log.logData(analysis_data, Utils.generatePartingLine("="));
                Log.logData(analysis_data, "+ Unit: " + as);
                Log.logData(analysis_data, "--- The passing variable [ " + as.getLeftOp() + " ] is re-defined.");
                // Save info.
                Log.logData(analysis_data, "+ Save information -- variable re-defined.");
                saveDataStructureAndRelatedInfo(base_unit, element_type, 0, redefined_variable, return_variable, entryBU_variables,
                        passingMapVariableToInflowItem, variableToField);
                // Update the passing variable set.
                removeVariable(redefined_variable, passing_variables, newVariableToCopy);
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
            return base_unit.getSourceDefs().get(as); // The element type corresponding to this AssignStmt.
        }
        return null;
    }

    public static void adjustVariableSetIfElementTypeUpdate(BU base_unit, String element_type, Value return_variable, Set<Value> entryBU_variables,
                                                            List<Unit> passing_units, List<Value> passing_variables,
                                                            Map<Value, String> passingMapVariableToInflowItem,
                                                            Map<Value, String> variableToField){
        if(element_type != null || !passing_variables.isEmpty()) {
            // Store some information before updating the element.
            Log.logData(analysis_data, Utils.generatePartingLine("="));
            Log.logData(analysis_data, "Save information -- element type update.");
            if(passing_variables.isEmpty()){
                passing_variables.add(null);
            }
            for(Value pv : passing_variables){
                saveDataStructureAndRelatedInfo(base_unit, element_type, 0, pv, return_variable, entryBU_variables,
                        passingMapVariableToInflowItem, variableToField);
            }
            passing_variables.clear();
            passing_units.clear();
        }
    }

    public static Map<String, Set<String>> filterUnsuitableDataStructures(Map<String, Set<String>> AETToDSs, List<BU> analyzed_base_units){
        Map<String, Set<String>> AETToDSs_new = new HashMap<>();
        for (Map.Entry<String, Set<String>> m_d_entry : AETToDSs.entrySet()){
            Set<String> data_structures = transferDSSetIfHaveUnknownMapItem(m_d_entry.getValue(), analyzed_base_units);
            Set<String> data_structures_new = Utils.deepCopy(data_structures);
            for(String ds : data_structures) {
                int flag_remove = 0;
                if (ds == null) {
                    flag_remove = 1;
                } else if (ds.contains("remove")) { // || s.contains("return") || s.startsWith("<")
                    continue;
                } else if (ds.contains("attribute") || ds.endsWith("Exception") || ds.endsWith("Failure")) {
                    flag_remove = 1;
                } else {
                    String type = ds.split("_")[0];
                    if (type.startsWith("<")) {
                        type = type.split(" ")[1];
                    }
                    if (type.endsWith("List") || type.endsWith("[]") || type.endsWith("Stack") || type.endsWith("Queue") ||
                            type.endsWith("Collection") || type.endsWith("Iterator") || type.endsWith("Map&Entry") ||
                            type.endsWith("StringBuilder")) {
                        flag_remove = 1;
                    } /*else if (type.endsWith("Map") || type.endsWith("SparseArray")) {
                        if (!ds.contains("_key")) {
                            flag_remove = 1;
                        }
                    }*/
                }
                if (flag_remove == 1) {
                    data_structures_new.remove(ds);
                }
            }
            if(!data_structures_new.isEmpty()) {
                AETToDSs_new.put(m_d_entry.getKey(), data_structures_new);
            }
        }
        System.out.println("=== Processed data structures: " + AETToDSs_new);
        return AETToDSs_new;
    }

    public static boolean needGenerateNewBaseUnit(int assignStmt, SootMethod method, Value base, Unit unit){
        String method_name = method.getName();
        String declaring_class;
        if (base != null) {
            declaring_class = ((RefType) base.getType()).getSootClass().getName();
        } else {
            declaring_class = method.getDeclaringClass().getName();
        }
        // We need to know which field that the tainted value is put into.
        if(method_name.equals("<init>")){
            if(declaring_class.endsWith("List") || declaring_class.endsWith("Map") || declaring_class.endsWith("SparseArray")
                    || declaring_class.endsWith("String") || declaring_class.endsWith("StringTokenizer" )
                    || declaring_class.endsWith("Array") || declaring_class.endsWith("Set")
                    || declaring_class.endsWith("Exception") || declaring_class.endsWith("Failure")){
                return false;
            }
            return true;
        }
        if(assignStmt == 1){
            AssignStmt as = (AssignStmt) unit;
            // We need to analysis the callee to confirm the tainted item of the tainted map value.
            if(Utils.isMapVariable(as.getLeftOp())){
                return true;
            }
            // We need to know which field that the tainted value is put into.
            if (method_name.startsWith("add") && !"add_addAll".contains(method_name)) {
                return true;
            } else if(method_name.startsWith("remove") && !"remove_removeAll".contains(method_name)){
                return true;
            }else if (method_name.startsWith("set") && !method_name.equals("set")){
                return true;
            } else if (method_name.startsWith("register") || method_name.startsWith("unregister")) {
                return true;
            } else{
                return false;
            }
        } else{
            if("add_addAll_remove_removeAll_set_put_putAll".contains(method_name)){
                return false;
            }
            return true;
        }
    }

    public static String getDataStructure(BU base_unit, int flag_remove, Value passing_variable, Value return_variable, Set<Value> entryBU_variables,
                                          Map<Value, String> passingMapVariableToInflowItem, Map<Value, String> variableToField){
        if (passing_variable == null) {
            return null;
        }

        // For the value put into an array, the final data structure should be the array.
        // r1[0] => r1
        passing_variable = Utils.getArrayVariable(passing_variable);

        String data_structure;
        // If the data structure is a field, store the whole field information.
        if (Utils.isFieldVariable(passing_variable)) {
            data_structure = "<" + passing_variable.toString().split(".<")[1];
            String cls = confirmBelongingClsOfField(base_unit, passing_variable);
            if(cls!=null){
                data_structure += "_" + cls + "(BC)";
            }
        } else if (variableToField.containsKey(passing_variable)) {
            data_structure = variableToField.get(passing_variable);
        } else {
            data_structure = passing_variable.getType().toString();
        }
        if(entryBU_variables!=null && entryBU_variables.contains(passing_variable)){
            data_structure += "_attribute";
        }
        // Flag the return variable.
        if(passing_variable.equals(return_variable)){
            data_structure += "_return";
        }
        if(flag_remove==1){
            data_structure += "_remove";
        }
        if(Utils.isMapVariable(passing_variable)){ // For the Map value, we need know whether the key or value is tainted.
            String item = passingMapVariableToInflowItem.get(passing_variable);
            if(item!=null) {
                data_structure += item;
            }else if(flag_remove==0){
                String msg = "Cannot find the inflow item of the Map value: " + passing_variable;
                Utils.terminate(msg);
            }
        }
        return data_structure;
    }

    public static Map<String, String> getEntryBridges(){
        Log.deleteData(entry_bridges);
        // Data preprocess.
        List<String> s_es = Log.readData(AnalysisForParsingClass2.target_settings);
        Map<String, Set<String>> targetSettingToElementTypes = new HashMap<>();
        for(String s_e : s_es){
            String setting = s_e.split("=>")[0].split("_")[0];
            String element_type = s_e.split("=>")[1];
            Set<String> element_types = targetSettingToElementTypes.get(setting); // One package setting may correspond to multiple element types.
            if(element_types == null){
                element_types  = new HashSet<>();
                element_types.add(element_type);
                targetSettingToElementTypes.put(setting, element_types);
            } else {
                element_types.add(element_type);
            }
        }
        String className = AnalysisForParsingClass2.parsedPackageSettingsClass; // The class for storing the parsed package's settings.
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        // Get the public fields of the class.
        List<String> public_fields = new ArrayList<>();
        for(SootField f : cls.getFields()){
            if(f.isPublic()){
                public_fields.add(f.getSignature());
            }
        }
        // Find the entry bridges for accessing the suspicious data structures.
        Map<String, String> entryBridgeToElementType = new HashMap<>();
        for(String f : targetSettingToElementTypes.keySet()){
            if(public_fields.contains(f)){ // The public field can be accessed through the corresponding class object.
                entryBridgeToElementType.put(f, targetSettingToElementTypes.get(f).toString());
            }
        }
        for(SootMethod method : cls.getMethods()){
            String method_name = method.getName();
            if(method_name.startsWith("get")) {
                Body body = method.retrieveActiveBody();
                Value return_value = null;
                String field = null;
                for (Unit unit : body.getUnits()) {
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        String likely_field = Utils.getFieldNameFromAssignStmt(as);
                        if(likely_field!=null){
                            if (targetSettingToElementTypes.keySet().contains(likely_field)) {
                                field = likely_field;
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
                            entryBridgeToElementType.put(method.getSignature(), targetSettingToElementTypes.get(field).toString());
                        }
                    }
                }
            }
        }
        for(Map.Entry<String, String> entry : entryBridgeToElementType.entrySet()){
            Log.logData(entry_bridges, entry.toString());
        }
        return entryBridgeToElementType;
    }

    public static Value getInvolvingRemovedStruct(int assignStmt, Value base, String callee_name, Unit unit){
        Value involved_removed_struct = null;
        if("remove_removeAll_delete_deleteAll".contains(callee_name)) {
            if (base != null) {
                involved_removed_struct = base;
            }
        }
        if(involved_removed_struct==null && assignStmt == 1) {
            AssignStmt as = (AssignStmt) unit;
            String likely_removed_struct = as.getLeftOp().getType().toString();
            if(likely_removed_struct.endsWith("List") || likely_removed_struct.endsWith("Map")
                    || likely_removed_struct.endsWith("SparseArray") || likely_removed_struct.endsWith("Set")) {
                involved_removed_struct = as.getLeftOp();
            }
        }
        return involved_removed_struct;
    }

    public static void saveDataStructureAndRelatedInfo(BU base_unit, String element_type, int flag_remove, Value passing_variable, Value return_variable,
                                                       Set<Value> entryBU_variables, Map<Value, String> passingMapVariableToInflowItem,
                                                       Map<Value, String> variableToField){
        String data_structure = getDataStructure(base_unit, flag_remove, passing_variable, return_variable, entryBU_variables,
                passingMapVariableToInflowItem, variableToField);
        String[] log_files = {analysis_data, method_data};
        // Merge the element types for this path and this base unit, respectively.
        String associated_element_type = getAssociatedElementType(base_unit.getAssociatedElementType(), element_type);
        base_unit.storeAssociatedElementTypeAndDataStructure(log_files, associated_element_type, data_structure);
        // Find the base-unit's farthest ancestor.
        SootMethod farthest_ancestor = base_unit.getBaseMethod();
        List<BU> parents = base_unit.getParents();
        if(parents!=null && !parents.isEmpty()) {
            farthest_ancestor = parents.get(0).getBaseMethod();
        }
        storeMethodAndCorrespondingAETAndDSs(farthest_ancestor, associated_element_type, data_structure);
    }

    public static void storeMethodAndCorrespondingAETAndDSs(SootMethod method, String associated_element_type, String data_structure) {
        Map<String, Set<String>> AETToDSs = methodToAETToDSs.get(method);
        if(AETToDSs == null) { // This key does not exist.
            AETToDSs = new HashMap<>();
        }
        Set<String> data_structures = AETToDSs.get(associated_element_type);
        if(data_structures == null) { // This key does not exist.
            data_structures = new HashSet<>();

        }
        data_structures.add(data_structure);
        AETToDSs.put(associated_element_type, data_structures);
        //out.println(AETToDSs);
        methodToAETToDSs.put(method, AETToDSs);
        //out.println(methodToAETToDSs);
    }

    public static void storeUsefulInfo(AssignStmt as, BU base_unit, Set<Value> entryBU_variable, Set<Value> identifier_variables, List<Value> source_variables,
                                       Map<Value, Value> newVariableToCopy, Map<Value, String> numericVariableToValue,
                                       Map<Value, String> passingMapVariableToInflowItem,
                                       Map<Value, String> variableToField){
        if(as==null) return;

        if (Utils.hasCopyOfVars(as, source_variables)) {
            Value source_var = as.getRightOp();
            Value copy = as.getLeftOp();
            if(!source_variables.contains(copy)) {
                source_variables.add(copy);
            }
            // For the situation that the source variable is Map-type.
            if(passingMapVariableToInflowItem.containsKey(source_var)){
                String inflow_map_item = passingMapVariableToInflowItem.get(source_var);
                storePassingMapVariableAndCorrespondingInflowItem(copy, inflow_map_item, newVariableToCopy, passingMapVariableToInflowItem);
            }
            // For the situation that the source variable is entry base unit-related.
            if(entryBU_variable.contains(source_var)){
                entryBU_variable.add(copy);
            }
            // For the situation that the source variable is identifier-related.
            if(identifier_variables.contains(source_var)){
                identifier_variables.add(copy);
            }
        }

        storeNewVariableAndCorrespondingCopy(as, newVariableToCopy);
        storeNumericVariableAndCorrespondingValue(as, numericVariableToValue);
        storeVariableAndCorrespondingField(as, base_unit, variableToField);
    }



    public static void updateEntryBURelatedVariableSet(int flag_attribute_entry, Value outflow_variable, Set<Value> entryBU_variables){
        if(outflow_variable == null || entryBU_variables == null) return;

        if(flag_attribute_entry == 1){
            entryBU_variables.add(outflow_variable);
            Log.logData(analysis_data, "--- Update the entry base-unit related variables: " + entryBU_variables);
        } else if(entryBU_variables.contains(outflow_variable)){ // This variable is no longer related to the entry base unit.
            entryBU_variables.remove(outflow_variable);
            Log.logData(analysis_data, "--- Remove the entry base-unit related variable: " + outflow_variable);
            Log.logData(analysis_data, "--- Update the entry base-unit related variables: " + entryBU_variables);
        }
    }

    public static void updatePassingVariableSet(Value outflow_variable, List<Value> inflow_passing_variables, List<Value> passing_variables,
                                                List<Value> source_variables, Map<Value, Value> newValueToCopy){
        // Update the passing variable set.
        if(!inflow_passing_variables.isEmpty()) {
            // Remove the inflow passing variable.
            for(Value var : inflow_passing_variables) {
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
            Log.logData(analysis_data, "--- Update the source variable set: " + source_variables);
        }
    }

    // Find the blocks that contains the noteworthy units and the first noteworthy unit (the start uint).
    public static Pair<List<Block>, Unit> findNoteworthyBlocksAndStartUnit(BU base_unit, CompleteBlockGraph cbg, List<Value> source_variables){
        List<Block> noteworthy_blocks = new ArrayList<>();
        Unit start_unit = null;
        Set<AssignStmt> source_defs = base_unit.getSourceDefs() != null ? base_unit.getSourceDefs().keySet() : null;
        for(Block block : cbg.getBlocks()){
            for(Unit unit : block){
                if(isNoteworthyUnit(base_unit, unit, source_variables, source_defs)){
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

    // For path-sensitive analysis.
    // Find the LCA block of all interested blocks (including the block in the interested blocks) .
    public static void keepUsefulInfoForSkippedBlocks(BU base_unit, CompleteBlockGraph cbg, int start_block_id, Set<Value> entryBU_variables, Set<Value> identifier_variables,
                                                      List<Value> source_variables, Map<Value, Value> newVariableToCopy, Map<Value, String> numericVariableToValue,
                                                      Map<Value, String> passingMapVariableToInflowItem, Map<Value, String> variableToField){

        for(Block block : cbg.getBlocks()){
            if(block.getIndexInMethod() == start_block_id){
                return;
            }
            for(Unit unit : block){
                //out.println("%%%% " + unit);
                // Store some information before we skip the unit.
                if(unit instanceof AssignStmt) {
                    AssignStmt as = (AssignStmt) unit;
                    storeUsefulInfo(as, base_unit, entryBU_variables, identifier_variables, source_variables, newVariableToCopy, numericVariableToValue,
                            passingMapVariableToInflowItem, variableToField);
                }
            }
        }
    }

    public static void findEntryBaseUnits(Map<String, String> entryBridgeToElementType, Set<SootMethod> processing_methods){
        //int method_num = 0;
        for(SootClass cls : Scene.v().getClasses()) {
            if (!cls.getPackageName().contains("android")) { // Non Android package.
                //out.println("cls (non-android): " + cls);
                continue;
            }
            if (cls.isInterface()) continue;
            if (cls.getName().equals(AnalysisForParsingClass2.parsedPackageSettingsClass)) continue;
            List<SootMethod> methods = cls.getMethods();
            if(methods.isEmpty()){
                continue;
            }
            for (int i = 0; i< methods.size(); i++) {
                SootMethod method = methods.get(i);
                if (!method.isConcrete()) continue;
                Body body;
                try {
                    body = method.retrieveActiveBody();
                } catch (Exception e) {
                    out.println("Soot cannot load method: " + method);
                    e.printStackTrace();
                    continue;
                }
                BU base_unit = new BU(method);
                List<Value> source_vars = new ArrayList<>();
                Map<AssignStmt, String> sourceDefToElementType = new HashMap<>();
                for (Unit unit : body.getUnits()) {
                    Value source_var = null;
                    String associated_element_type = null;
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                        String likely_field = Utils.getFieldNameFromAssignStmt(as);
                        if (likely_field != null) {
                            if (entryBridgeToElementType.keySet().contains(likely_field)) {
                                source_var = as.getLeftOp();
                                associated_element_type = entryBridgeToElementType.get(likely_field);
                            }
                        } else if (ie != null) {
                            SootMethod callee = ie.getMethod();
                            if (callee.isConcrete()) {
                                String callee_sig = callee.getSignature();
                                if (entryBridgeToElementType.keySet().contains(callee_sig)) {
                                    source_var = as.getLeftOp();
                                    associated_element_type = entryBridgeToElementType.get(callee_sig);
                                }
                            } else if (callee.isAbstract()) {
                                String callee_subSig = callee.getSubSignature();
                                for (String eb : entryBridgeToElementType.keySet()) {
                                    if (eb.contains(callee_subSig)) {
                                        SootMethod implemented_method = getImplementedMethodOfAbstractMethod(null, ie, base_unit);
                                        if (implemented_method != null && implemented_method.getSignature().equals(eb)) {
                                            source_var = as.getLeftOp();
                                            associated_element_type = entryBridgeToElementType.get(eb);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        if (source_var != null) {
                            if(!source_vars.contains(source_var)) {
                                source_vars.add(source_var);
                            }
                            sourceDefToElementType.put(as, associated_element_type);
                        }
                    }
                }
                if (!source_vars.isEmpty()) {
                    Log.logData(processing_methods_baseInfo, Utils.generatePartingLine("="));
                    Log.logData(processing_methods_baseInfo, "+ Method: " + method.getSignature() +
                            "\n+ Source Variables: " + source_vars);
                    base_unit.setSourceVariables(source_vars);
                    //base_unit.setBaseElement(base_element_types.toString());
                    base_unit.setSourceDefs(sourceDefToElementType);
                    base_units.offer(base_unit);
                    processing_methods.add(method);
                }
            }
        }
    }

    public static void dataFlowAnalysisForPath(BU base_unit, int path_sensitive, List<Block> blocks, List<String> generated_bu_sigs, List<Integer> path,
                                               List<Value> source_variables, Set<Value> entryBU_variables, Set<Value> identifier_variables,
                                               Set<Value> null_variables, Map<Value, Value> newVariableToCopy, Map<Value, String> numericVariableToValue,
                                               Map<Value, String> passingMapVariableToInflowItem, Map<Value, String> variableToField) {
        Unit start_unit = base_unit.getStartUnit();
        Set<AssignStmt> source_defs = base_unit.getSourceDefs() != null ? base_unit.getSourceDefs().keySet() : null;

        // Copy the map.
        // Be specific to this path.
        Map<Value, Value> newVariableToCopy_path = Utils.deepCopy(newVariableToCopy);
        Map<Value, String> numericVariableToValue_path = Utils.deepCopy(numericVariableToValue);
        Map<Value, String> passingMapVariableToInflowItem_path = Utils.deepCopy(passingMapVariableToInflowItem);
        Map<Value, String> variableToField_path = Utils.deepCopy(variableToField);
        List<Value> source_variables_path = Utils.deepCopy(source_variables);
        Set<Value> entryBU_variables_path = Utils.deepCopy(entryBU_variables);
        Set<Value> identifier_variables_path = Utils.deepCopy(identifier_variables);
        Set<Value> null_variables_path = Utils.deepCopy(null_variables);

        int flag_analysis = 0;
        String element_type = null; // The element type related to this path.
        Value return_variable = null; // A path has 0 or 1 return value.

        List<Value> passing_variables = new ArrayList<>();
        List<Unit> passing_units = new ArrayList<>();

        for (int i = 0; i< path.size(); i++) {
            int block_id = path.get(i);
            Block block = blocks.get(block_id);
            for (Unit unit : block) {
                flag_analysis = canStartAnalysis(flag_analysis, start_unit, path_sensitive, unit, source_defs);
                if(flag_analysis == 0) {
                    //out.println("@@@@ " + unit);
                    // Store the useful info before skipping this unit.
                    if(unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        storeUsefulInfo(as, base_unit, entryBU_variables_path, identifier_variables_path, source_variables_path, newVariableToCopy_path,
                                numericVariableToValue_path, passingMapVariableToInflowItem_path, variableToField_path);
                    }
                    continue;
                }
                //out.println("==== " + unit);

                InvokeExpr ie = null;
                Value base = null;
                SootMethod callee = null;
                String callee_name = "NULL";

                int need_analysis = 0;
                int assignStmt = 0;
                int flag_attribute = 0; // Flag that whether the passing variable is the attribute of previously passing variable.
                int flag_attribute_entry = 0; // Flag that whether the passing variable is the attribute of the entry base unit.
                List<Value> inflow_source_vars = new ArrayList<>(); // The source variables that this unit contains.
                List<Value> inflow_passing_vars = new ArrayList<>(); // The passing variables that this unit contains.

                if(unit instanceof TableSwitchStmt){
                    String msg = "TableSwitchStmt: " + unit;
                    Utils.terminate(msg);
                }

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
                            String msg = "+ Wrong path, stop analyzing!" + "\n--- " + is + "\n --- Null variable set: " + null_variables_path +
                                    "\n--- Numeric variable set: " + numericVariableToValue_path;
                            Utils.logMsg(analysis_data, msg, "!");
                            return;
                        }
                        continue;
                    }
                }

                // A statement needs to be analysed only if it contains the entry / tainted value.
                if (unit instanceof AssignStmt) {
                    assignStmt = 1;
                    AssignStmt as = (AssignStmt) unit;
                    ie = Utils.getInvokeOfAssignStmt(as);
                    inflow_source_vars = hasRightVarsOfAssignStmt(as, base_unit, analysis_data, source_variables_path);
                    inflow_passing_vars = hasRightVarsOfAssignStmt(as, base_unit, analysis_data, passing_variables);
                    if(!inflow_source_vars.isEmpty() || !inflow_passing_vars.isEmpty()){
                        need_analysis = 1;
                    }
                    // This source / passing variable has been re-defined.
                    if (need_analysis == 0) {
                        String new_element_type = adjustVariableSetIfVariableRedefined(as, base_unit, element_type, ie, return_variable, entryBU_variables_path,
                                source_defs, passing_units, passing_variables, source_variables_path, newVariableToCopy_path,
                                passingMapVariableToInflowItem_path, variableToField_path);
                        if(new_element_type!=null && !new_element_type.equals(element_type)){ // Element type update;
                            String msg = "+ Unit: " + unit + "\n--- Update the element type: " + element_type + " => " + new_element_type;
                            Utils.logMsg(analysis_data, msg, "+");
                            adjustVariableSetIfElementTypeUpdate(base_unit, element_type, return_variable, entryBU_variables_path, passing_units, passing_variables,
                                    passingMapVariableToInflowItem_path, variableToField_path);
                            // Update the element type
                            element_type = new_element_type;
                        }
                    }
                    // Store useful information.
                    storeUsefulInfo(as, base_unit, entryBU_variables_path, identifier_variables_path, source_variables_path,  newVariableToCopy_path,
                            numericVariableToValue_path, passingMapVariableToInflowItem_path, variableToField_path);
                } else if (unit instanceof InvokeStmt) {
                    ie = ((InvokeStmt) unit).getInvokeExpr();
                    base = Utils.getBaseOfInvokeExpr(ie);
                    callee_name = ie.getMethod().getName();
                    inflow_source_vars = hasParamsOfInvokeExpr(base_unit, ie, analysis_data, source_variables_path);
                    inflow_passing_vars = hasParamsOfInvokeExpr(base_unit, ie, analysis_data, passing_variables);
                    if(!inflow_source_vars.isEmpty() || !inflow_passing_vars.isEmpty()) {
                        need_analysis = 1;
                    } else if(callee_name.equals("toArray")){
                        if(source_variables_path.contains(base)){
                            inflow_source_vars.add(base);
                            need_analysis = 1;
                        } else if (passing_variables.contains(base)){
                            inflow_passing_vars.add(base);
                            need_analysis = 1;
                        }
                    }
                }

                if (ie != null) {
                    callee = ie.getMethod();
                    callee_name = callee.getName();
                    base = Utils.getBaseOfInvokeExpr(ie);
                }

                if (need_analysis == 0){
                    continue;
                }

                Log.logData(analysis_data, Utils.generatePartingLine("="));
                Log.logData(analysis_data, "+ Unit: " + unit);
                if (!inflow_source_vars.isEmpty()) {
                    Log.logData(analysis_data, "--- Inflow source variables: " + inflow_source_vars);
                }
                if(!inflow_passing_vars.isEmpty()){
                    Log.logData(analysis_data, "--- Inflow passing variables: " + inflow_passing_vars);
                }
                // Focus on the source / passing variable and its attributes.
                // If the source / passing variable is passed in the callee, generate a new base-unit.
                Set<Integer> inflow_param_indices = getInflowParamIndices(base_unit, ie, analysis_data, inflow_passing_vars, inflow_source_vars);
                if (!inflow_param_indices.isEmpty()) {
                    Log.logData(analysis_data, "--- Inflow callee.");
                    if (canSkipForInflowParam(base, callee, callee_name)) {
                        Log.logData(analysis_data, "--- Can skip, pass.");
                        continue;
                    }
                    // For the inflow method related to data removing, we record the involved data struct.
                    if(callee_name.startsWith("remove") || callee_name.startsWith("delete")){
                        Value involved_removed_var = getInvolvingRemovedStruct(assignStmt, base, callee_name, unit);
                        if(involved_removed_var!=null) {
                            Log.logData(analysis_data, Utils.generatePartingLine("="));
                            Log.logData(analysis_data, "Save information -- data removing.");
                            saveDataStructureAndRelatedInfo(base_unit, element_type, 1, involved_removed_var, return_variable, entryBU_variables_path,
                                    passingMapVariableToInflowItem_path, variableToField_path);
                            continue;
                        }
                    }
                    if ("add_addAll_put_putAll_append".contains(callee_name)) { // xxx.add(passing variable)
                        if (base != null) {
                            Value outflow_var = base;
                            // Update the Map-type variable info.
                            if(Utils.isMapVariable(base)){
                                updatePassingMapVariableInfo(null, ie, analysis_data, callee_name, outflow_var, identifier_variables_path, inflow_param_indices,
                                        passing_units, newVariableToCopy_path, passingMapVariableToInflowItem_path);
                            }
                            // Update the passing variable set.
                            updatePassingVariableSet(outflow_var, inflow_passing_vars,  passing_variables, source_variables_path, newVariableToCopy_path);
                            passing_units.add(unit);
                            continue;
                        }
                    }
                    if (callee_name.equals("arraycopy")) {
                        if(!inflow_param_indices.contains(0)) {
                            Log.logData(analysis_data, "--- No data flow, pass");
                            continue;
                        }
                        // Update the passing variable set.
                        Value outflow_var = ie.getArg(2);
                        updatePassingVariableSet(outflow_var, inflow_passing_vars, passing_variables, source_variables_path, newVariableToCopy_path);
                        passing_units.add(unit);
                        continue;
                    }
                    if (callee.isConstructor()) { // Constructor should be record, because the passing variable will be put into a field.
                        if (base != null) {
                            // Update the passing variable set.
                            Value outflow_var = base;
                            updatePassingVariableSet(outflow_var, inflow_passing_vars, passing_variables, source_variables_path, newVariableToCopy_path);
                            passing_units.add(unit);
                        }
                    }
                    // Generate new base-unit.
                    if (needGenerateNewBaseUnit(assignStmt, callee, base, unit)) {
                        if(callee.isAbstract()){
                            // Confirm the implemented method when the callee is abstract.
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            callee = getImplementedMethodOfAbstractMethod(analysis_data, ie, base_unit);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                        }
                        BU new_base_unit = generateNewBaseUnit(base_unit, callee, unit, element_type, ie, analysis_data, generated_bu_sigs, entryBU_variables_path,
                                inflow_param_indices, identifier_variables_path, null_variables_path, numericVariableToValue_path,
                                passingMapVariableToInflowItem_path, null,
                                null, variableToField_path);
                        if(new_base_unit!=null){ // This callee has not been recorded.
                            base_units.offer(new_base_unit);
                        }
                    }
                    // For the constructor, we have update the passing variable set before.
                    if(callee.isConstructor()){
                        continue;
                    }
                    // For the inflow method related to data removing, we don't update the passing variable set.
                    if(callee_name.startsWith("remove") || callee_name.startsWith("delete")
                            || callee_name.startsWith("unregister")){
                        Log.logData(analysis_data, "--- Data removing method, no need to update variable set, pass");
                        continue;
                    }
                    // Judge whether the passing variable is an attribute of the entry base-unit.
                    int attribute_type = isAttrOfPassingVar(ie, callee_name, entryBU_variables_path, inflow_param_indices);
                    if(attribute_type == 1){
                        flag_attribute = 1;
                    } else if(attribute_type == 2){
                        flag_attribute = 1;
                        flag_attribute_entry = 1;
                    }
                } else {
                    if (base != null) {
                        if (inflow_source_vars.contains(base) || inflow_passing_vars.contains(base)) {
                            Log.logData(analysis_data, "--- Inflow base.");
                            if(canSkipForInflowBase(base, callee_name)){
                                Log.logData(analysis_data, "--- Can skip, pass.");
                                continue;
                            }
                            if(assignStmt == 0 && callee_name.equals("toArray") && (!ie.getArgs().isEmpty())){
                                // Update the passing variable.
                                Value outflow_var = ie.getArg(0);
                                updatePassingVariableSet(outflow_var, inflow_passing_vars,  passing_variables, source_variables_path, newVariableToCopy_path);
                                passing_units.add(unit);
                                continue;
                            }
                            // Judge whether the passing variable is an attribute of the entry base-unit.
                            int attribute_type = isAttrOfPassingVar(base, callee_name, entryBU_variables_path);
                            if(attribute_type == 1){
                                flag_attribute = 1;
                            }else if(attribute_type == 2){
                                flag_attribute = 1;
                                flag_attribute_entry = 1;
                            }
                        }
                    }
                }

                // Update the passing variable set.
                if (assignStmt == 1) {
                    AssignStmt as = (AssignStmt) unit;
                    // There is a copy of source variable.
                    if(Utils.hasCopyOfVars(as, source_variables_path)){
                        Log.logData(analysis_data, "--- Copy the source variable." + "\n--- Update the source variable set: " +
                                source_variables);
                        continue;
                    }
                    // Judge whether the passing variable is an attribute of the entry base-unit.
                    if (ie == null) {
                        String right_op = as.getRightOp().toString();
                        if (right_op.startsWith("lengthof")) {
                            Log.logData(analysis_data, "--- Get length, pass.");
                            continue;
                        }
                        int attribute_type = isAttrOfPassingVar(as, entryBU_variables_path);
                        if(attribute_type == 1){
                            flag_attribute = 1;
                        } else if(attribute_type == 2){
                            flag_attribute = 1;
                            flag_attribute_entry = 1;
                        }
                    }
                    Value outflow_var = as.getLeftOp();
                    // Update the identifier info.
                    updateIdentifierRelatedVariable(as, base_unit.getBaseMethod().getName(), analysis_data, identifier_variables_path);
                    // Update the Map-type variable information.
                    updatePassingMapVariableInfo(as, ie, analysis_data, callee_name, outflow_var, identifier_variables_path, inflow_param_indices,
                            passing_units, newVariableToCopy_path, passingMapVariableToInflowItem_path);
                    // Record the attribute to distinguish the passing variables more finely.
                    updateEntryBURelatedVariableSet(flag_attribute_entry, outflow_var, entryBU_variables_path);
                    // Update the passing variable set.
                    // If the outflow variable is the attribute of the previously passing variable,
                    // or the previously passing variable involves a judgement, record it.
                    if((flag_attribute == 1 && !"iterator".contains(callee_name) && !callee_name.startsWith("next")
                            && !as.getRightOp().toString().startsWith("("))
                            || outflow_var.getType().toString().equals("boolean")){
                        addVariable(outflow_var, passing_variables, newVariableToCopy_path);
                        Log.logData(analysis_data, "--- Update the passing variable set: " + passing_variables);
                    } else {
                        updatePassingVariableSet(outflow_var, inflow_passing_vars, passing_variables, source_variables_path, newVariableToCopy_path);
                    }
                }
                passing_units.add(unit);
            }
        }

        // Store some information.
        Log.logData(analysis_data, Utils.generatePartingLine("="));
        Log.logData(analysis_data, "Save information-- analysis complete.");
        if(source_variables_path.contains(return_variable)){
            passing_variables.add(return_variable);
        }
        if(passing_variables.isEmpty()){
            passing_variables.add(null);
        }
        for(Value pv : passing_variables) {
            saveDataStructureAndRelatedInfo(base_unit, element_type, 0, pv, return_variable, entryBU_variables_path,
                    passingMapVariableToInflowItem_path, variableToField_path);
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
        Set<Value> entryBU_variables = new HashSet<>(); // The variables related to the entry base-unit's source variables.
        Set<Value> identifier_variables = new HashSet<>(); // The variable related to an identifier (name or tag or process).
        Set<Value> null_variables = new HashSet<>(); // The variable with the null constant.
        Map<Value, String> passingMapVariableToInflowItem = new HashMap<>(); // The passing Map-type variable's corresponding inflow item info.
        Map<Value, String> numericVariableToValue = new HashMap<>(); // The concrete value of all numeric variables (iX, bX, zX).
        Map<Value, String> variableToField = new HashMap<>(); // The variable related to a field.
        initializeUsefulInfo(base_unit, body, source_variables, entryBU_variables, identifier_variables, null_variables, numericVariableToValue,
                passingMapVariableToInflowItem, null, null, variableToField);

        Utils.printPartingLine("=");
        System.out.println("+ Base method: " + base_method.getName() + "\n+ Base-unit sig: " + base_unit_sig + "\n+ Source variables: " +
                source_variables + "\n+ Base element type: " + base_unit.getAssociatedElementType());
        //Log.
        Log.logData(analysis_data, "+ Source variables: " + source_variables + "\n+ Base element type: " +
                base_unit.getAssociatedElementType());

        //Log data.
        Log.logData(method_data, Utils.generatePartingLine("#"));
        Log.logData(method_data, "+ Method: " + base_method.getSignature() + "\n+ Base-unit sig: " + base_unit_sig);

        // Construct the block graph.
        CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        Log.logBody(body, store_base_path);
        Log.logCBG(cbg, store_base_path);

        // Find noteworthy blocks.
        System.out.println("Find noteworthy blocks ...");
        Pair<List<Block>, Unit> noteworthy_info = findNoteworthyBlocksAndStartUnit(base_unit, cbg, source_variables);
        List<Block> noteworthy_blocks = noteworthy_info.getO1();
        Unit start_unit = noteworthy_info.getO2();
        if(noteworthy_blocks.isEmpty()){ // No need to analyze.
            String[] log_files = {analysis_data, method_data};
            Log.logData(analysis_data, Utils.generatePartingLine("="));
            Log.logData(analysis_data,  "This method dose not need to analyze.");
            base_unit.storeAssociatedElementTypeAndDataStructure(log_files, null, null);
            String msg = "Cannot find the noteworthy block. Analyze the next base unit.";
            Utils.printMsg(msg, "!");
            return;
        }
        // Confirm analysis model.
        out.println("Confirm analysis model ...");
        int path_sensitive = 1;
        int start_block_id = cbg.getHeads().get(0).getIndexInMethod();
        int analysis_model = confirmAnalysisModel(base_method.getName(), cbg, noteworthy_blocks);
        out.println("+ Analysis model (0: flow-insensitive, 1: from the head block, 2: from the LCA block): " + analysis_model);
        if(analysis_model != 1) {
            if (analysis_model == 0) { // Flow-insensitive analysis.
                base_unit.setStartUnit(start_unit); // For path-sensitive analysis, different path may have different start unit. So we only set the start unit for this model.
                start_block_id = noteworthy_blocks.get(0).getIndexInMethod();
                path_sensitive = 0;
                List<Integer> path = new ArrayList<>();
                for (int i = start_block_id; i < cbg.getBlocks().size(); i++) {
                    path.add(i);
                }
                Graph.paths.add(path);
                Graph.path_num = 1;
            } else { // Start analyzing from the LCA.
                start_block_id = Graph.getLeastCommonAncestorOfBlocks(noteworthy_blocks);
            }
            if (start_block_id == -1) {
                String msg = "Illegal start block id: " + base_method.getSignature();
                Utils.terminate(msg);
            }
            // Since in mode 0 / 2, we will not start analysis from the head block.
            // We need to store some useful info before we skip some blocks.
            keepUsefulInfoForSkippedBlocks(base_unit, cbg, start_block_id, entryBU_variables, identifier_variables, source_variables, newVariableToCopy,
                    numericVariableToValue, passingMapVariableToInflowItem, variableToField);
        }

        System.out.println("+ Start block id: " + start_block_id + "\n+ Parameters: " + base_unit.getParameters() + "\n+ EntryBU variables: " + entryBU_variables +
                "\n+ Numeric variables: " + numericVariableToValue + "\n+ Field variables: " + variableToField);

        // Log data.
        Log.logData(analysis_data, "+ Base method parameters:" + base_unit.getParameters() + "\n+ Start block id: " + start_block_id +
                "\n+ EntryBU variables: " + entryBU_variables + "\n+ Identifiers: " + identifier_variables + "\n+ Null variables: " + null_variables +
                "\n+ Passing Map variable: " + passingMapVariableToInflowItem + "\n+ Numeric variables: " + numericVariableToValue +
                "\n+ Element type variables: " + "\n+ Field variables: " + variableToField);

        // Start analysis.
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

        int analyzed_path_num = 0;
        List<String> generated_BU_sigs = new ArrayList<>();  // Avoid duplicated generating, because multiple paths may involve the same methods.
        while(!Graph.paths.isEmpty()) {
            List<Integer> path = Graph.paths.get(0);
            analyzed_path_num+=1;
            Graph.paths.remove(0);
            Log.logData(analysis_data, Utils.generatePartingLine(">"));
            Log.logData(analysis_data, "+ Path " + analyzed_path_num +": " + path);
            dataFlowAnalysisForPath(base_unit, path_sensitive, cbg.getBlocks(), generated_BU_sigs, path, source_variables, entryBU_variables,
                    identifier_variables, null_variables, newVariableToCopy, numericVariableToValue,
                    passingMapVariableToInflowItem, variableToField);
            if(analyzed_path_num == total_path_num|| analyzed_path_num % 1000 == 0) {
                System.out.println("Analyzed path num: " + analyzed_path_num);
            }
            //Utils.pause();
        }
    }

    public static void identifySuspiciousMethods(){
        // Clear previous logs.
        Log.deleteData(processing_methods_baseInfo);
        Log.deleteData(entry_bridges);

        Log.deleteData(method_data);
        Log.deleteData(analysis_data);

        Log.deleteData(processing_method_data);
        Log.deleteData(suspicious_methods);
        Log.deleteData(suspicious_methods_final);
        Log.deleteData(suspicious_method_names);
        Log.deleteData(suspicious_methods_final_names);

        String[] skip_mds = {"isEmpty", "byteSizeOf", "size", "length", "forEachPackage", "obtainAttributes", "skipCurrentTag", "unknownTag", "recycle"};
        String[] skip_cls = {"com.android.internal.util.AnnotationValidations","java.io.PrintWriter", "android.os.AsyncTask", "android.content.res.XmlResourceParser",
                "org.xmlpull.v1.XmlPullParser", "android.content.pm.parsing.result.ParseInput", "android.util.Slog"};

        String[] pims = {"generateWithoutComponentsUnchecked", "assertPackageIsValid", "preparePackageLI", "scanPackageOnlyLI",
                "addPackageInternal", "restorePermissionState", "shouldGrantPermissionByProtectionFlags",
                "grantRuntimePermissionInternal"}; // "setAllowlistedRestrictedPermissionsInternal"

        //String[] pims = {"preparePackageLI", "scanPackageOnlyLI"}; // "setAllowlistedRestrictedPermissionsInternal"
        skip_methods.addAll(new ArrayList<>(Arrays.asList(skip_mds)));
        skip_classes.addAll(new ArrayList<>(Arrays.asList(skip_cls)));
        flow_insensitive_methods.addAll(new ArrayList<>(Arrays.asList(pims)));

        System.out.println("Find entry base-units ...");
        Map<String, String> entryBridgesToElementType = getEntryBridges();
        Set<SootMethod> processing_methods = new HashSet<>();
        findEntryBaseUnits(entryBridgesToElementType, processing_methods);
        System.out.println("Done. Processing method num: " + processing_methods.size());
        Utils.printPartingLine("+");
        //Utils.pause();
        List<BU> analyzed_base_units = new ArrayList<>();

        while (!base_units.isEmpty()) {
            BU base_unit = base_units.poll();
            SootMethod base_method = base_unit.getBaseMethod();
            String associated_element_type = base_unit.getAssociatedElementType();

            //if(!base_method.getName().equals("preparePackageLI")) continue;

            Log.logData(analysis_data, Utils.generatePartingLine("#"));
            Log.logData(analysis_data, "+ Analyzed method: " + base_method);
            if(base_method.getName().startsWith("dump")){
                Log.logData(analysis_data, "--- Dump method, pass.");
                Utils.printPartingLine("=");
                System.out.println("+ Method: " + base_method.getName());
                System.out.println("+ Pass.");
                continue;
            }

            String base_unit_sig = generateSignatureOfBaseUnit(base_unit);
            Log.logData(analysis_data, "+ Base-unit sig: " + base_unit_sig.split("&")[1]);
            int flag_analyzed = 0;
            for (BU abu : analyzed_base_units) {
                String atp_Sig = generateSignatureOfBaseUnit(abu);
                if (atp_Sig.equals(base_unit_sig)) {
                    Log.logData(analysis_data, "--- This method has been analyzed.");
                    flag_analyzed = 1; // This base method has been analyzed.
                    base_unit.setParameters(abu.getParameters()); // The same base methods have the same parameters.
                    base_unit.setStartUnit(abu.getStartUnit()); // The same base units have the same start unit.
                    base_unit.setSourceDefs(abu.getSourceDefs()); // The same base units have the same source definitions.
                    List<Pair<String, String>> e_ds = abu.getAssociatedElementTypesAndDataStructures();
                    base_unit.setAssociatedElementTypesAndDataStructures(e_ds); // The same base methods have the same data structure info.
                    if (e_ds!= null) {
                        SootMethod farthest_ancestor = base_method; // Analyzed base unit and this base unit have different ancestor method.
                        List<BU> parents = base_unit.getParents();
                        if(parents!=null && !parents.isEmpty()) {
                            farthest_ancestor = parents.get(0).getBaseMethod();
                        }
                        for (Pair<String, String> e_d : e_ds) {
                            storeMethodAndCorrespondingAETAndDSs(farthest_ancestor, e_d.getO1(), e_d.getO2());
                        }
                    }
                    Set<BU> children = abu.getPassingChildren(); // Analyzed base unit and this base unit have different parents.
                    base_unit.setPassingChildren(children); // The same base methods have the same passing children.
                    if (children != null) {
                        List<BU> new_parents = Utils.deepCopy(base_unit.getParents());
                        new_parents.add(base_unit);
                        for (BU child : children) {
                            BU new_base_unit = new BU(child.getBaseMethod(), associated_element_type, child.getCallUnit(), new_parents, child.getEntryBUParamIndies(),
                                    child.getIdentifierParamIndices(), child.getInflowParamIndices(), child.getNullParamIndices(), child.getInflowMapParamIndies(),
                                    null, null,  child.getFieldParamIndies(),
                                    child.getNumericParamIndies());
                            base_units.offer(new_base_unit); // Record the passing base-units.
                        }
                    }
                    break;
                }
            }

            if (flag_analyzed == 1) {
                analyzed_base_units.add(base_unit);
                continue;
            }

            analyzed_base_units.add(base_unit);
            dataFlowAnalysisForBaseUnit(base_unit);

            //Utils.pause();
        }

        Utils.printPartingLine("#");
        System.out.println("Processing method num: " + processing_methods.size());
        System.out.println("Analyzed processing method num: " + methodToAETToDSs.size());

        int suspicious_method_num = 0;
        int suspicious_method_num_final = 0;
        for(Map.Entry<SootMethod, Map<String, Set<String>>> m_e_d_entry : methodToAETToDSs.entrySet()){
            SootMethod method = m_e_d_entry.getKey();
            String method_sig = method.getSignature();
            String out = method_sig + " & ";
            Map<String, Set<String>> AETToDSs = m_e_d_entry.getValue();
            Log.logData(processing_method_data, Utils.generatePartingLine("#"));
            Log.logData(processing_method_data, "+ Method: " + method_sig);
            for(Map.Entry<String, Set<String>> e_d_entry : AETToDSs.entrySet()){
                String associated_element_type = e_d_entry.getKey();
                Set<String> data_structures = transferDSSetIfHaveUnknownMapItem(e_d_entry.getValue(), analyzed_base_units);
                Log.logData(processing_method_data, Utils.generatePartingLine("="));
                Log.logData(processing_method_data, "+ Associated element type: " + associated_element_type);
                for(String ds : data_structures) {
                    Log.logData(processing_method_data, Utils.generatePartingLine("-"));
                    Log.logData(processing_method_data, "-- Data structure: " + ds);
                }
                out += associated_element_type + "=" + data_structures + " & ";
            }
            System.out.println(out);
            // Filter secure methods.
            Map<String, Set<String>> AETToDSs_filtered = filterUnsuitableDataStructures(AETToDSs, analyzed_base_units);
            int flag_deduplicate = 1;
            if(!AETToDSs_filtered.isEmpty()) { // Suspicious method.
                suspicious_method_num += 1;
                Log.logData(suspicious_methods, Utils.generatePartingLine("#"));
                Log.logData(suspicious_methods, "+ Method: " + method_sig);
                String method_name = Utils.getMethodNameFromMethodSig(method_sig);
                Log.logData(suspicious_method_names, "+ Method name: " + method_name);
                if (!isDeDuplicateTargetSetting(AETToDSs_filtered)) { // Filter FP
                    flag_deduplicate = 0;
                    suspicious_method_num_final += 1;
                    Log.logData(suspicious_methods_final, Utils.generatePartingLine("#"));
                    Log.logData(suspicious_methods_final, "+ Method: " + method_sig);
                    Log.logData(suspicious_methods_final_names, "+ Method name: " + method_name);
                }
            }
            for(Map.Entry<String, Set<String>> e_d_entry : AETToDSs_filtered.entrySet()) {
                String associated_element_type = e_d_entry.getKey();
                Set<String> data_structures = e_d_entry.getValue();
                Log.logData(suspicious_methods, Utils.generatePartingLine("="));
                Log.logData(suspicious_methods, "+ Associated element type: " + associated_element_type);
                if(flag_deduplicate == 0) {
                    Log.logData(suspicious_methods_final, Utils.generatePartingLine("="));
                    Log.logData(suspicious_methods_final, "+ Associated element type: " + associated_element_type);
                }
                for(String ds : data_structures) {
                    Log.logData(suspicious_methods, Utils.generatePartingLine("-"));
                    Log.logData(suspicious_methods, "-- Data structure: " + ds);
                    if (flag_deduplicate == 0) {
                        Log.logData(suspicious_methods_final, Utils.generatePartingLine("-"));
                        Log.logData(suspicious_methods_final, "-- Data structure: " + ds);
                    }
                }
            }
        }
        System.out.println("Suspicious method number: " + suspicious_method_num);
        System.out.println("Suspicious method number (remove deduplicate): " + suspicious_method_num_final);
    }
}
