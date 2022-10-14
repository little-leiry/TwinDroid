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

import static java.lang.System.exit;

public class AnalysisForParsingClass extends Analysis{
    // The class for parsing an apk.
    public static final String parsing_class = "android.content.pm.parsing.ParsingPackageUtils";
    // The class for store the parsed package's settings.
    public static final String parsedPackage_settings_class = "android.content.pm.parsing.ParsingPackageImpl";

    // The tainted_methods needed to be analysed.
    // Each object consists of <tainted method, tainted value, associated element>
    // Use queue to do BFS.
    public static Queue<Tainted> tainted_points = new LinkedList<Tainted>();

    // element name => data structures.
    public static Map<String, Set<String>> associatedElementToDataStructures = new HashMap<String, Set<String>>();

    // skip_names: important names. These names are unlikely an element name.
    public static List<String> skip_names = new ArrayList<>();

    // skip_methods, skip_classes: important methods / classes. If a statement contains this kind of methods / classes, just skipping this statement.
    public static List<String> skip_methods = new ArrayList<>();
    public static List<String> skip_classes = new ArrayList<>();

    // no_analyzed_methods, no_analyzed_classes: these methods' / classes' functions have been known, no need to be analyzed.
    public static List<String> no_analyzed_classes = new ArrayList<>();
    public static List<String> no_analyzed_methods = new ArrayList<>();

    public static final String element_data = "logs/parsing/element_data.txt";
    public static final String method_data = "logs/parsing/method_data.txt";
    public static String analysis_data = "logs/parsing/analysis_data.txt";
    public static String suspicious_structures = "logs/parsing/suspicious_structures.txt";

    public static boolean isInterestedUnit(Unit unit, List<Value> entry_value_copies, Map<Value, String> valueToLikelyElement){
        if(unit instanceof AssignStmt){
            AssignStmt as =(AssignStmt) unit;
            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- Related to elements.
            if (getRelatedElement(ie, valueToLikelyElement) != null) {
                return true;
            }
            // Interested unit -- the entry value appears in the right of the Assignment unit.
            if(!Utils.hasRightValueOfAssignStmt(as, entry_value_copies).isEmpty()) {
                // Filter some uninterested types.
                if(Utils.hasCopyOfValues(as, entry_value_copies)){
                    return false;
                }
                if (ie == null && as.getUseBoxes().size() == 2) {
                    if (! as.getLeftOp().toString().contains(".<") && ! as.getRightOp().toString().startsWith("(")) {
                        return false;
                    }
                }
                if (entry_value_copies.contains(base)) {
                    String base_type = base.getType().toString();
                    String method_name = ie.getMethod().getName();
                    if(canFilterForTaintedBase(base_type, method_name)){
                        return false;
                    }
                }
                if (!Utils.hasParameterOfInvokeStmt(ie, entry_value_copies).isEmpty()) {
                    SootMethod method = ie.getMethod();
                    String method_name = method.getName();
                    int flag_array=0;
                    for(Value entry : entry_value_copies){
                        if(entry.getType().toString().equals("android.content.res.TypedArray")){
                            flag_array = 1;
                            break;
                        }
                    }
                    if(canFilterForTaintedParameter(base, method, method_name, flag_array)){
                        return false;
                    }
                }
                return true;
            }
        } else if (unit instanceof InvokeStmt) {
            InvokeExpr ie = ((InvokeStmt) unit).getInvokeExpr();
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- Pass in the entry value as a parameter.
            if (!Utils.hasParameterOfInvokeStmt(ie, entry_value_copies).isEmpty()) {
                SootMethod method = ie.getMethod();
                String method_name = method.getName();
                int flag_array=0;
                for(Value entry : entry_value_copies){
                    if(entry.getType().toString().equals("android.content.res.TypedArray")){
                        flag_array = 1;
                        break;
                    }
                }
                if(canFilterForTaintedParameter(base, method, method_name, flag_array)){
                    return false;
                }
                return true;
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

    // Treat the tainted / entry value as a whole, ignore the part (ie., the attribution) of it.
    public static boolean canFilterForTaintedBase(String base_type, String method_name){
        if (base_type.endsWith("parsing.result.ParseResult")) {
            if (method_name.equals("getResult")) { // result.getResult()
                return false;
            }
        }
        if (base_type.equals("android.content.res.TypedArray")){
            return false;
        }
        if(base_type.equals("java.util.StringTokenizer")){
            if(method_name.equals("nextToken")){
                return false;
            }
        }
        if (method_name.startsWith("to")){ // Type transformation of the value.
            return false;
        }
        if(base_type.equals("java.lang.Integer")){ // Type transformation of the value (when the value's type is Integer).
            if(method_name.endsWith("Value")){
                return false;
            }
        }
        if(base_type.equals("android.util.TypedValue")){ // Type transformation of the value (when the value's type is TypedValue).
            if(method_name.contains("To")){
                return false;
            }
        }
        if("intern_charAt".contains(method_name)){ // Normalized the value
            return false;
        }
        if(base_type.equals("java.lang.String")){ // Normalized the value (when the value's type is String).
            if(method_name.equals("replace")){
                return false;
            }
        }
        if (method_name.equals("get")) {
            if (base_type.endsWith("List") || base_type.endsWith("Map")) {
                return false;
            }
        }
        return true;
    }

    public static boolean canFilterForTaintedParameter(Value base, SootMethod method, String method_name, int flag_array){
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
        if (method_name.startsWith("remove") || (flag_array == 0 && method_name.startsWith("get"))) {
            return true;
        }
        return false;
    }

    public static boolean needRecordMethod(int assignStmt, int flag_parser, String callee_name){
        if(assignStmt == 1){
            if(flag_parser == 1){
                return true;
            } else if (callee_name.startsWith("add") && !callee_name.equals("add")){
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

    // The return element is related to the current analyze method and its parents.
    public static String getAssociatedElement(String outer_element, String inner_element){
        if(outer_element == null){
            return inner_element;
        }else if(inner_element == null) {
            return outer_element;
        } else {
            return outer_element + "_" + inner_element;
        }
    }

    public static String getRelatedElement(InvokeExpr ie, Map<Value, String> valueToLikelyElement){
        if(ie == null) return null;

        String method_name = ie.getMethod().getName();
        Value base = Utils.getBaseOfInvokeExpr(ie);

        if (method_name.equals("equals")) {
            if (ie.getArg(0) instanceof StringConstant) { // parser.getName().equals(element)
                String s = ie.getArg(0).toString();
                if (!skip_names.contains(s) && ! s.startsWith("\"android.permission") && !s.startsWith("\"/")) {
                    return s;
                }
            } else if (base != null && valueToLikelyElement!=null) { // element.equals(parser.getName())
                if (valueToLikelyElement.containsKey(base)) {
                    return valueToLikelyElement.get(base);
                }
            }
        }
        return null;
    }

    // associated element: related to the current analyzed method and its parents.
    public static void storeAssociatedElementAndCorrespondingDataStructure(String associated_element, String data_structure) {
        if(associated_element==null) return;

        /*if (data_structure == null){
            data_structure = "NUll";
        } else if (data_structure.endsWith("parsing.result.ParseResult")){ // The parse result of this element has not been solved completely.
            return;
        }*/

        Set<String> ds = associatedElementToDataStructures.get(associated_element);
        if (ds == null) { // This key does not exist.
            ds = new HashSet<>();
            ds.add(data_structure);
            associatedElementToDataStructures.put(associated_element, ds);
        } else {
            ds.add(data_structure);
        }
    }

    // This statement is likely related to an element.
    public static void storeValueAndCorrespondingLikelyElement(AssignStmt as, Map<Value, String> valueToLikelyElement){
        List<ValueBox> vbs = as.getUseBoxes();
        if (vbs.size()==1 && vbs.get(0).getValue() instanceof StringConstant) {
            Value element_value = as.getLeftOp();
            String likely_element = as.getUseBoxes().get(0).getValue().toString();
            if(likely_element.startsWith("\"/")) return;
            if(likely_element.startsWith("\"android.permission")) return;
            if (skip_names.contains(likely_element)) return;
            valueToLikelyElement.put(element_value, likely_element);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "Likely element: " + as);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
        }
    }

    public static void storeUsefulInfo(Unit unit, List<Value> entry_value_copies, Map<Value, Value> newValeToCopy, Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToLikelyElement){
        if(unit==null) return;

        if(unit instanceof AssignStmt) {
            AssignStmt as = (AssignStmt) unit;
            if (Utils.hasCopyOfValues(as, entry_value_copies)) {
                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                Log.logData(analysis_data, "--- Copy entry value: " + as);
                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                Value copy = as.getLeftOp();
                if(!entry_value_copies.contains(copy)) {
                    entry_value_copies.add(copy);
                }
            }
            storeNewValueAndCorrespondingCopy(as, newValeToCopy);
            storeValueAndCorrespondingLikelyElement(as, valueToLikelyElement);
            storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment);
        }
    }

    public static void transformEntryValue(List<Value> entry_value_copies, Body body, boolean special_method){
        if(entry_value_copies == null || body == null) return;

        if(! entry_value_copies.get(0).getType().toString().equals("android.content.res.XmlResourceParser")){
            entry_value_copies.clear();
            return;
        }

        Value new_entry_value = null;
        for(Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                if(ie!=null && ie.getMethod().getName().equals("obtainAttributes")){
                    if(Utils.hasParameterOfInvokeStmt(ie, entry_value_copies) != null){
                        new_entry_value = as.getLeftOp();
                        break;
                    }
                }
            }
        }
        if(new_entry_value != null) {
            if (special_method) { // The method implements multiple analysis method.
                entry_value_copies.add(new_entry_value);
            } else {
                entry_value_copies.clear();
                entry_value_copies.add(new_entry_value);
            }
        }
    }

    public static void updateTaintedValues(Value newly_tainted_value, List<Value> involved_tainted_values, List<Value> tainted_values, Map<Value, Value> newValueToCopy, String callee_name){
        // Update the tainted value.
        if(!involved_tainted_values.isEmpty()) {
            // Remove the previously tainted value.
            for(Value v : involved_tainted_values) {
                if (v.getType().toString().endsWith("parsing.result.ParseResult") && !callee_name.equals("getResult")) {
                    Log.logData(analysis_data, "--- Cannot update the tainted value.");
                    return;
                }
                removePreviouslyTaintedValue(v, tainted_values, newValueToCopy);
            }
        }
        // Add the newly tainted value.
        addNewlyTaintedValue(newly_tainted_value, tainted_values, newValueToCopy);
        Log.logData(analysis_data, "--- Update the tainted value: " + tainted_values);
    }

    public static Block findStartBlock(CompleteBlockGraph cbg, Tainted entry, List<Value> entry_value_copies, Map<Value, Value> newValueToCopy,
                                       Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToLikelyElement){
        if(cbg==null || entry == null || entry_value_copies == null) return null;

        Block start_block = null;
        int store_param = entry.getParameters() == null? 1:0;
        for(Block block : cbg.getBlocks()){
            for(Unit unit : block){
                if(store_param == 1) {
                    if (unit instanceof IdentityStmt) {
                        IdentityStmt is = (IdentityStmt) unit;
                        storeParameterOfTaintedPoint(entry, is);
                        continue;
                    }
                }
                if(isInterestedUnit(unit, entry_value_copies, valueToLikelyElement)){
                    System.out.println("Interested unit: " + unit);
                    entry.setStartUnit(unit);
                    start_block = block;
                    break;
                }
                if (unit instanceof SwitchStmt){
                    // For switch-case statement, we need to analyze each case.
                    SwitchStmt ss = (SwitchStmt) unit;
                    for (int i = 0; i < ss.getTargets().size(); i++) {
                        Unit u = ss.getTarget(i);
                        if(isInterestedUnit(u, entry_value_copies, valueToLikelyElement)){
                            System.out.println("Interested unit: " + unit);
                            entry.setStartUnit(unit);
                            start_block = block;
                            break;
                        }
                    }
                    if(start_block!=null) break;
                }
                // Store some information before we skip the unit.
                storeUsefulInfo(unit, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment, valueToLikelyElement);
            }
            if(start_block != null) break;
        }
        return start_block;
    }

    // Find the method for starting to parse the AndroidManifest.xml
    public static void findEntryPoints() {
        List<SootMethod> methods = Utils.getMethodsOfClass(parsing_class);
        for (SootMethod sm : methods) {
            if (sm.isConcrete()) {
                Body body = sm.retrieveActiveBody();
                for (Unit unit : body.getUnits()) {
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        InvokeExpr callee = Utils.getInvokeOfAssignStmt(as);
                        if (callee != null) {
                            // find the entry point
                            String calleeName = callee.getMethod().getName();
                            if (calleeName.equals("openXmlResourceParser")) {
                                for (Value v : callee.getArgs()) {
                                    if (v instanceof StringConstant) {
                                        String parameterName = v.toString();
                                        if (parameterName.equals("\"AndroidManifest.xml\"")) {
                                            List<Value> entry_values = new ArrayList<>();
                                            entry_values.add(as.getLeftOp());
                                            tainted_points.offer(new Tainted(sm, entry_values));
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

    // skip_names: important names. These names are unlikely an element name.
    // skip_methods, skip_classes: important methods / classes. If a statement contains this kind of methods / classes, just skipping this statement.
    // no_analyzed_methods, no_analyzed_classes: these methods' / classes' functions have been known, no need to be analyzed.
    public static void dataFlowAnalysisForBlocks(List<Block> blocks, List<Integer> block_ids, Tainted entry, List<Value> entry_value_copies,
                                                 Map<Value, Value> newValueToCopy, Map<Value, String> numericValueToConcreteAssignment,
                                                 List<String> recorded_tainted_points, Map<Value, String> valueToLikelyElement) {

        String entry_element = entry.getOuterElement();
        Unit start_unit = entry.getStartUnit();
        List<Tainted> entry_parents = entry.getParents();

        // Copy the map.
        // Specific to this path.
        Map<Value, String> numericValueToConcreteAssignment_path = Utils.deepCopy(numericValueToConcreteAssignment);
        Map<Value, String> valueToLikelyElement_path = Utils.deepCopy(valueToLikelyElement);
        List<Value> entry_values_path = Utils.deepCopy(entry_value_copies);

        Value case_value = null; // The bridge value between two LookupSwithStmts.
        String element = null; // This element only related to entry method.
        String data_structure = null;

        List<Value> tainted_values = new ArrayList<>();
        Unit tainted_unit = null;
        Map<Value, String> mapValueToTaintedItem = new HashMap<>();

        int flag_start = 0;

        for (int i = 0; i< block_ids.size(); i++) {
            int block_id = block_ids.get(i);
            Block block = blocks.get(block_id);
            for (Unit unit : block) {
                // Analysis should start with the start unit.
                if (start_unit.equals(unit)) {
                    flag_start = 1;
                }
                if (flag_start == 0) {
                    continue;
                }

                InvokeExpr ie = null;
                Value base = null;
                SootMethod callee = null;
                String callee_name = "NULL";

                int need_analysis = 0;
                int assignStmt = 0;
                List<Value> involved_entry_values = new ArrayList<>(); // The entry values that this unit contains.
                List<Value> involved_tainted_values = new ArrayList<>(); // The tainted values that this unit contains.

                // Store useful information from this unit.
                storeUsefulInfo(unit, entry_values_path, newValueToCopy, numericValueToConcreteAssignment_path, valueToLikelyElement_path);

                // Filter wrong paths.
                if (unit instanceof LookupSwitchStmt) {
                    LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                    if (case_value == null) { // Get the bridge case value between two LookupSwitchStmts.
                        case_value = getCaseValue(lss);
                    } else if (lss.getKey().equals(case_value)) {
                        boolean wrong_path = isWrongPathForSwitchStmt(analysis_data, blocks, block_ids, i, lss, case_value, numericValueToConcreteAssignment_path);
                        if (wrong_path) {
                            Utils.generatePartingLine("!");
                            Log.logData(analysis_data, "Wrong path, stop analyzing!");
                            Utils.generatePartingLine("!");
                            return;
                        }
                        // Finish transformation, reset the case value.
                        case_value = null;
                    }
                    continue;
                }

                if(unit instanceof IfStmt){
                    IfStmt is = (IfStmt) unit;
                    boolean wrong_path = isWrongPathForIfStmt(blocks, block_ids, i, is, numericValueToConcreteAssignment_path);
                    if (wrong_path) {
                        Utils.generatePartingLine("!");
                        Log.logData(analysis_data, "--- Wrong path, stop analyzing!");
                        Utils.generatePartingLine("!");
                        return;
                    }
                    continue;
                }

                // A statement needs to be analysed only if it contains the entry / tainted value.
                if (unit instanceof AssignStmt) {
                    assignStmt = 1;
                    AssignStmt as = (AssignStmt) unit;
                    ie = Utils.getInvokeOfAssignStmt(as);
                    involved_entry_values = Utils.hasRightValueOfAssignStmt(as, entry_value_copies);
                    involved_tainted_values = Utils.hasRightValueOfAssignStmt(as, tainted_values);
                    if(!involved_entry_values.isEmpty() || !involved_tainted_values.isEmpty()){
                        need_analysis = 1;
                    }
                    // This entry / tainted value has been re-defined.
                    if (need_analysis == 0) {
                        Value redefined_value = hasRedefinedValue(as, ie, entry_values_path, tainted_unit);
                        if (redefined_value != null) {
                            entry_values_path.remove(redefined_value);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(analysis_data, "+ Unit: " + as);
                            Log.logData(analysis_data, "--- The entry value [ " + as.getLeftOp() + " ] is re-defined, remove it.");
                            Log.logData(analysis_data, "--- Updated the entry value: " + entry_values_path);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                        } else {
                            redefined_value = hasRedefinedValue(as, ie, tainted_values, tainted_unit);
                            if (redefined_value!=null) {
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                Log.logData(analysis_data, "+ Unit: " + as);
                                Log.logData(analysis_data, "--- The tainted value [ " + as.getLeftOp() + " ] is re-defined.");
                                data_structure = getDataStructure(redefined_value, mapValueToTaintedItem); // Store some information when the tainted value is redefined.
                                Log.logData(analysis_data, "Store the information -- value re-defined.");
                                entry.storeInnerElementAndStructure(element, data_structure); // This element only related to the entry method.
                                String associated_element = getAssociatedElement(entry_element, element); // This element related to the entry method and its parents.
                                storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
                                removePreviouslyTaintedValue(redefined_value, tainted_values, newValueToCopy);
                                tainted_unit = null;
                                Log.logData(analysis_data, "--- Update the tainted value: " + tainted_values);
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            }
                        }
                    }
                } else if (unit instanceof InvokeStmt) {
                    ie = ((InvokeStmt) unit).getInvokeExpr();
                    involved_entry_values = Utils.hasParameterOfInvokeStmt(ie, entry_values_path);
                    involved_tainted_values = Utils.hasParameterOfInvokeStmt(ie, tainted_values);
                    if(!involved_entry_values.isEmpty() || !involved_tainted_values.isEmpty()) {
                        need_analysis = 1;
                    }
                }

                if (ie != null) {
                    callee = ie.getMethod();
                    callee_name = callee.getName();
                    base = Utils.getBaseOfInvokeExpr(ie);
                }

                // Get the element's name.
                String s = getRelatedElement(ie, valueToLikelyElement_path);
                if (s != null){
                    // Store some information before update the element.
                    // Have solved one element case.
                    // Or have tainted some values that irrelevant to this element.
                    String old_element = element;
                    if(old_element != null || !tainted_values.isEmpty()) {
                        // Store some information before updating the element.
                        Log.logData(analysis_data, Utils.generatePartingLine("="));
                        Log.logData(analysis_data, "Store information -- element update.");
                        if(tainted_values.isEmpty()){
                            tainted_values.add(null);
                        }
                        for(Value v : tainted_values){
                            data_structure = getDataStructure(v, mapValueToTaintedItem);
                            entry.storeInnerElementAndStructure(old_element, data_structure); // This element only related to the entry method.
                            String associated_element = getAssociatedElement(entry_element, old_element); // This element related to the entry method and its parents.
                            storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
                        }
                        tainted_values.clear();
                        tainted_unit = null;
                    }
                    // Update the element.
                    element = s;
                    Log.logData(analysis_data, Utils.generatePartingLine("+"));
                    Log.logData(analysis_data, "Element: " + element);
                    Log.logData(analysis_data, Utils.generatePartingLine("+"));
                    continue;
                }

                if (need_analysis == 0){
                    continue;
                }

                Log.logData(analysis_data, Utils.generatePartingLine("="));
                Log.logData(analysis_data, "+ Unit: " + unit);
                if (!involved_entry_values.isEmpty()) {
                    Log.logData(analysis_data, "--- Tainted by the entry value.");
                }
                if(!involved_tainted_values.isEmpty()){
                    Log.logData(analysis_data, "--- Tainted value: " + tainted_values);
                }

                // If the tainted / entry value is passed in the callee, this callee is tainted.
                Set<Integer> tainted_param_indices = new HashSet<>();
                if(!involved_entry_values.isEmpty()){
                    for(Value v : involved_entry_values){
                        Integer param_index = Utils.isParameterOfInvokeStmt(ie, v);
                        if(param_index!=-1){
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if(!involved_tainted_values.isEmpty()){
                    for(Value v : involved_tainted_values){
                        Integer param_index = Utils.isParameterOfInvokeStmt(ie, v);
                        if(param_index!=-1){
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if(!tainted_param_indices.isEmpty()){
                    Log.logData(analysis_data, "--- Tainted callee.");
                    int flag_array = 0;
                    int flag_parser = 0;
                    for(int param_index : tainted_param_indices){
                        String param_type = ie.getArg(param_index).getType().toString();
                        if(param_type.equals("android.content.res.TypedArray")){
                            flag_array = 1;
                        } else if(param_type.equals("android.content.res.XmlResourceParser")){
                            flag_parser = 1;
                        }
                    }
                    if(canFilterForTaintedParameter(base, callee, callee_name, flag_array)){
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    if(callee.isConstructor()){
                        if(base != null){
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy, callee_name);
                            tainted_unit = unit;
                            continue;
                        }
                    }
                    if (callee_name.equals("add") || callee_name.equals("put")) { // add(tainted_value), put(tainted_value)
                        if (base != null) {
                            // Update the Map value information.
                            if(base.getType().toString().contains("Map")){
                                System.out.println(tainted_param_indices);
                                String tainted_item = confirmTaintedItemOfMap(callee_name, tainted_param_indices);
                                storeMapValueAndCorrespondingTaintedItem(base, tainted_item, mapValueToTaintedItem, newValueToCopy);
                            }
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy, callee_name);
                            tainted_unit = unit;
                            continue;
                        } else if(assignStmt == 1){
                            // Update the Map value information.
                            AssignStmt as = (AssignStmt) unit;
                            if(as.getLeftOp().getType().toString().contains("Map")){
                                String tainted_item = confirmTaintedItemOfMap(callee_name, tainted_param_indices);
                                storeMapValueAndCorrespondingTaintedItem(as.getLeftOp(), tainted_item, mapValueToTaintedItem, newValueToCopy);
                            }
                        }
                    }
                    if(callee_name.equals("arraycopy")){
                        // Update the tainted value.
                        Value newly_tainted_value = ie.getArg(2);
                        updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy, callee_name);
                        tainted_unit = unit;
                        continue;
                    }
                    if(needRecordMethod(assignStmt, flag_parser, callee_name)){
                        if (ie instanceof InterfaceInvokeExpr) { // Invoke an abstract method, try to get its body.
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                            callee = getImplementedMethodOfAbstractMethod(analysis_data, ifi, entry);
                            Log.logData(analysis_data,Utils.generatePartingLine("+"));
                        }
                        List<Value> tainted_parameters = new ArrayList<>();
                        for(int param_index : tainted_param_indices) {
                            Value parameter = Utils.getParameterOfMethod(callee, param_index);
                            if(parameter!=null){
                                tainted_parameters.add(parameter);
                            } else {
                                Utils.printPartingLine("!");
                                System.out.println("Null parameter.");
                                System.out.println("method: " + callee.getSignature());
                                System.out.println("parameter index: " + param_index);
                                Utils.printPartingLine("!");
                                exit(0);
                            }
                        }
                        String tainted_point_sig = callee.hashCode() + tainted_parameters.hashCode() + element;
                        if(!recorded_tainted_points.contains(tainted_point_sig)) { // This tainted point has not been stored.
                            Log.logData(analysis_data, "--- Record the tainted method: " + callee_name);
                            recorded_tainted_points.add(tainted_point_sig);
                            entry.storeTaintedChildren(new Tainted(callee, tainted_parameters, element, unit)); // This element only related to entry method.
                            String associated_element = getAssociatedElement(entry_element, element); // This element related to entry method and its parents.
                            List<Tainted> parents = Utils.deepCopy(entry_parents);
                            parents.add(entry);
                            tainted_points.offer(new Tainted(callee, tainted_parameters, associated_element, parents, unit));
                        } else {
                            Log.logData(analysis_data, "--- This tainted method has been recoded.");
                        }
                    }
                } else {
                    // Treat the tainted / entry value as a whole, ignore the part (ie., the attribution) of it.
                    if (base != null) {
                        if (tainted_values.contains(base) || entry_values_path.contains(base)) {
                            Log.logData(analysis_data, "--- Tainted base.");
                            String base_type = base.getType().toString();
                            if(canFilterForTaintedBase(base_type, callee_name)){
                                Log.logData(analysis_data, "--- Pass.");
                                continue;
                            }
                        }
                    }
                }

                // Pass the tainted value.
                if (assignStmt == 1) {
                    AssignStmt as = (AssignStmt) unit;
                    // There is a copy of entry value.
                    if(Utils.hasCopyOfValues(as, entry_values_path)){
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    // Treat the tainted / entry value as a whole, ignore the part (ie.e., the attribution) of it.
                    // Apart from the TypeValue data -- r9 = $r8.<android.util.TypedValue: java.lang.CharSequence string>
                    // i1 = $r8.<android.util.TypedValue: int data>
                    // Transfer the type of the tainted -- r6 = (java.util.Set) $r10;
                    // Assign the value to a filed --
                    // r0.<android.content.pm.parsing.ParsingPackageImpl: java.util.List permissions> = $r2;
                    if (ie == null && as.getUseBoxes().size() == 2) {
                        String left_op = as.getLeftOp().toString();
                        String right_op = as.getRightOp().toString();
                        int flag_pass = 1;
                        if(left_op.contains(".<") || right_op.startsWith("(")){
                            flag_pass = 0;
                        } else if(right_op.contains(".<")){
                            if(as.getUseBoxes().get(1).getValue().getType().toString().equals("android.util.TypedValue")){
                                if(right_op.contains("string") || right_op.contains("data")){
                                    flag_pass = 0;
                                }
                            }
                        }
                        if(flag_pass == 1) {
                            Log.logData(analysis_data, "--- Pass.");
                            continue;
                        }
                    }
                    // Update the Map value information.
                    if(ie == null && as.getLeftOp().getType().toString().contains("Map") && mapValueToTaintedItem.containsKey(as.getRightOp())){
                        String tainted_item = mapValueToTaintedItem.get(as.getRightOp());
                        storeMapValueAndCorrespondingTaintedItem(as.getLeftOp(), tainted_item, mapValueToTaintedItem, newValueToCopy);
                    }
                    // Update the tainted value.
                    Value newly_tainted_value = as.getLeftOp();
                    updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy,callee_name);
                }
                tainted_unit = unit;
            }
        }

        // Store some information.
        Log.logData(analysis_data, Utils.generatePartingLine("="));
        Log.logData(analysis_data, "Store information -- analyze completely.");
        if(tainted_values.isEmpty()){
            tainted_values.add(null);
        }
        for(Value v : tainted_values) {
            data_structure = getDataStructure(v, mapValueToTaintedItem);
            entry.storeInnerElementAndStructure(element, data_structure); // This element only related to the entry method.
            String associated_element = getAssociatedElement(entry_element, element); // This element related to the entry method and its parents.
            storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
        }
    }

    public static void dataFlowAnalysisForMethod(Tainted entry){
        SootMethod entry_method = entry.getMethod();
        Body body = null;
        if (entry_method.isConcrete()) {
            body = entry_method.retrieveActiveBody();
        } else {
            Utils.printPartingLine("!");
            System.out.println("This method does not have a body.");
            Utils.printPartingLine("!");
            exit(0);
        }
        // Construct the block graph.
        CompleteBlockGraph cbg = new CompleteBlockGraph(body);

        Log.logBody(body);
        Log.logCBG(cbg);

        Utils.printPartingLine("=");
        System.out.println("+ Method: " + entry_method.getName());
        System.out.println("+ Entry value: " + entry.getTaintedValues());


        Map<Value, String> valueToLikelyElement = new HashMap<Value, String>(); // The Values whose concrete value is String.
        Map<Value, String> numericValueToConcreteAssignment = new HashMap<Value, String>(); // The concrete value of all numeric Values (iX, bX, zX).
        Map<Value, Value> newValueToCopy = new HashMap<Value, Value>(); // The newly constructed object and its copy.

        List<Value> entry_value_copies = Utils.deepCopy(entry.getTaintedValues());

        // To avoid path explosion caused by massive blocks, we start our analysis with the block we are interested in.
        // Because we ignore some blocks directly, we need save some useful information from them.
        System.out.println("Find start block...");
        // The general analysis method -- treats the element parser as a whole and gets its parse result.
        // The secondary analysis method -- gets the attributions of the element parser.
        // The special methods implement multiple analysis methods.
        boolean special_method = isSpecialMethod(entry_method.getName());
        if(special_method){
            transformEntryValue(entry_value_copies, body, true);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "Transform the entry value :" + entry_value_copies);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
        }
        Block start_block = findStartBlock(cbg, entry, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment, valueToLikelyElement);
        if(start_block == null){
            if(special_method){
                Utils.printPartingLine("!");
                System.out.println("Cannot find the start block of the special method: " + entry_method.getSignature());
                Utils.printPartingLine("!");
                exit(0);
            }
            // These methods do not implement the general analysis methods.
            // We need transform the entry value.
            System.out.println("Cannot find the start block, transform the entry value...");
            transformEntryValue(entry_value_copies, body, false);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "Cannot find the start block, transform the entry value :" + entry_value_copies);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            // Find the start block again.
            start_block = findStartBlock(cbg, entry, entry_value_copies,newValueToCopy, numericValueToConcreteAssignment, valueToLikelyElement);
            if(start_block == null) { // This method no needs to analysis.
                entry.storeInnerElementAndStructure(null, null);
                entry.storeTaintedChildren(null);
                Log.logData(analysis_data, "Still cannot find, this method does not need to be analyzed.");
                Utils.printPartingLine("!");
                System.out.println("Cannot find the start block.");
                Utils.printPartingLine("!");
                return;
            }
        }

        System.out.println("+ Start block id: " + start_block.getIndexInMethod());
        System.out.println("+ numeric: " + numericValueToConcreteAssignment);
        System.out.println("+ likely_element: " + valueToLikelyElement);

        // Log data.
        Log.logData(analysis_data, "+ Parameters:" + entry.getParameters());
        Log.logData(analysis_data, "+ Start block id: " + start_block.getIndexInMethod());

        System.out.println("Generate path...");
        Graph.generatePathsFromBlock(start_block);
        boolean duplicated = Utils.hasDuplicatedItems(Graph.paths);
        if(duplicated) {
            Utils.printPartingLine("!");
            System.out.println("Exist duplicated paths.");
            Utils.printPartingLine("!");
            exit(0);
        } else {
            System.out.println("No duplicated paths.");
        }

        int total_num = Graph.paths.size();
        System.out.println("+ Total path num: " + total_num);
        if(total_num > 50000){
            System.out.println("To many paths.");
            Log.logData(analysis_data, "Path number > 50000, change.");
            Graph.paths.clear();
            List<Integer> path = new ArrayList<>();
            for (int i = start_block.getIndexInMethod(); i < cbg.getBlocks().size(); i++) {
                path.add(i);
            }
            Graph.paths.add(path);
        }

        //Log data.
        Log.logData(method_data, Utils.generatePartingLine("#"));
        Log.logData(method_data, "+ Method: " + entry_method.getSignature());

        int path_num = 0;
        List<String> recorded_tainted_points = new ArrayList<>();  // Avoid duplicated recoding, because multiple paths may involve the same methods.
        while(!Graph.paths.isEmpty()) {
            List<Integer> path = Graph.paths.get(0);
            Graph.paths.remove(0);
            Log.logData(analysis_data, Utils.generatePartingLine(">"));
            Log.logData(analysis_data, "+ Path: " + path);
            dataFlowAnalysisForBlocks(cbg.getBlocks(), path, entry, entry_value_copies, newValueToCopy,
                    numericValueToConcreteAssignment, recorded_tainted_points, valueToLikelyElement);
            path_num+=1;
            if(path_num == total_num || path_num % 1000 == 0) {
                System.out.println("Analyzed path num: " + path_num);
            }
            //Utils.pause();
        }
    }

    public static void findSuspiciousDataStructures(){
        Log.deleteData(element_data);
        Log.deleteData(method_data);
        Log.deleteData(analysis_data);
        Log.deleteData(suspicious_structures);


        String[] skip_nms = {"\"android\"", "\"array\"", "\"singleInstancePerTask\""};
        String[] skip_mds = {"append", "obtainAttributes", "skipCurrentTag", "unknownTag"};
        String[] no_analysis_mds = {"max", "min", "create", "digit", "composeLongVersionCode", "computeMinSdkVersion", "computeTargetSdkVersion"};
        String[] skip_cls = {"android.content.res.XmlResourceParser", "android.content.pm.parsing.result.ParseInput", "com.android.internal.util.AnnotationValidations", "android.util.Slog"};
        String[] no_analysis_cls = {"com.android.internal.util.CollectionUtils", "android.text.TextUtils", "com.android.internal.util.ArrayUtils", "android.content.pm.parsing.FrameworkParsingPackageUtils"};
        skip_names.addAll(new ArrayList<>(Arrays.asList(skip_nms)));
        skip_methods.addAll(new ArrayList<>(Arrays.asList(skip_mds)));
        no_analyzed_methods.addAll(new ArrayList<>(Arrays.asList(no_analysis_mds)));
        skip_classes.addAll(new ArrayList<>(Arrays.asList(skip_cls)));
        no_analyzed_classes.addAll(new ArrayList<>(Arrays.asList(no_analysis_cls)));

        findEntryPoints();

        List<Tainted> analyzed_tainted_points = new ArrayList<>();

        while (!tainted_points.isEmpty()) {
            Tainted tainted_point = tainted_points.poll();
            SootMethod tainted_method = tainted_point.getMethod();
            String tainted_element = tainted_point.getOuterElement();
            List<Value> tainted_values = tainted_point.getTaintedValues();
            int flag_analyzed = 0;

            for(Tainted atp : analyzed_tainted_points){
                if(atp.getMethod().equals(tainted_method) && atp.getTaintedValues().equals(tainted_values)) {
                    flag_analyzed = 1; // This tainted method has been analyzed.
                    tainted_point.setParameters(atp.getParameters()); // The same tainted methods have the same parameters.
                    List<Pair<String, String>> e_ds = atp.getInnerElementAndStructure();
                    tainted_point.setInnerElementsAndStructures(e_ds); // The same tainted methods have the same <element, structure>.
                    if(e_ds != null) {
                        for (Pair<String, String> e_d : e_ds) {
                            String e = e_d.getO1();
                            String d = e_d.getO2();
                            String associated_element = getAssociatedElement(tainted_element, e); // This element is related to the tainted method and its parents.
                            storeAssociatedElementAndCorrespondingDataStructure(associated_element, d);
                        }
                    }
                    // If this method tainted other methods, store their information.
                    Set<Tainted> children = atp.getTaintedChildren();
                    tainted_point.setTaintedChildren(children); // The same tainted methods have the same tainted children.
                    if(children != null) {
                        List<Tainted> parents = Utils.deepCopy(tainted_point.getParents());
                        parents.add(tainted_point);
                        for (Tainted child : children) {
                            String element = child.getOuterElement(); // This element only associate with the tainted method.
                            String associated_element = getAssociatedElement(tainted_element, element); // This element associate with the tainted method and its parents.
                            tainted_points.offer(new Tainted(child.getMethod(), child.getTaintedValues(), associated_element, parents, child.getCallUnit()));
                        }
                    }
                    break;
                }
            }

            if(flag_analyzed==1) {
                analyzed_tainted_points.add(tainted_point);
                continue;
            }

            Log.logData(analysis_data, Utils.generatePartingLine("#"));
            Log.logData(analysis_data, "+ Analyzed method: " + tainted_method);
            Log.logData(analysis_data, "+ Entry value: " + tainted_point.getTaintedValues());
            analyzed_tainted_points.add(tainted_point);
            dataFlowAnalysisForMethod(tainted_point);

            //Utils.pause();
            //sleep(2000);
        }

        for(Map.Entry<String, Set<String>> entry: associatedElementToDataStructures.entrySet()){
            String associated_element = entry.getKey();
            Log.logData(element_data, Utils.generatePartingLine("="));
            Log.logData(element_data, "+ associated element: " + associated_element);
            String out = entry.getKey()+",";
            for(String ds : entry.getValue()){
                Log.logData(element_data, Utils.generatePartingLine("*"));
                Log.logData(element_data, "+ data structure: " + ds);
                out += ds + ",";
                if(ds!=null && ds.contains(".<") && ds.contains(parsedPackage_settings_class)) {
                    String type = ds.split(" ")[1];
                    if (type.contains("list") || type.contains("List") || type.contains("[]") || type.contains("Queue") || type.contains("Stack")) {
                        Log.logData(suspicious_structures, ds + "=>" + associated_element);
                        for (Tainted point : analyzed_tainted_points) {
                            List<Pair<String, String>> e_ds = point.getInnerElementAndStructure();
                            for (Pair<String, String> e_d : e_ds) {
                                String element = getAssociatedElement(point.getOuterElement(), e_d.getO1());
                                if (associated_element.equals(element) && ds.equals(e_d.getO2())) {
                                    Log.logData(element_data, Utils.generatePartingLine("-"));
                                    Log.logData(element_data, "+ call path:");
                                    for (Tainted parent : point.getParents()) {
                                        Log.logData(element_data, "--- " + parent.getMethod().getSignature());
                                    }
                                    Log.logData(element_data, "---" + point.getMethod().getSignature());
                                }
                            }
                        }
                    }
                }
            }
            System.out.println(out);
        }
    }
}
