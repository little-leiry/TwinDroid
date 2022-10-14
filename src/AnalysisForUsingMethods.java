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

public class AnalysisForUsingMethods extends Analysis{

    // The tainted_methods needed to be analysed.
    // Each object consists of <tainted method, tainted value, associated element>
    // Use queue to do BFS.
    public static Queue<Tainted> tainted_points = new LinkedList<Tainted>();

    // <method, associated element> => data structures.
    public static Map<Pair<SootMethod, String>, Set<String>> methodAndElementToDataStructures = new HashMap<Pair<SootMethod, String>, Set<String>>();

    // skip_names: important names. These names are unlikely an element name.
    public static List<String> skip_names = new ArrayList<>();

    // skip_methods, skip_classes: important methods / classes. If a statement contains this kind of methods / classes, just skipping this statement.
    public static List<String> skip_methods = new ArrayList<>();
    public static List<String> skip_classes = new ArrayList<>();

    // no_analyzed_methods, no_analyzed_classes: these methods' / classes' functions have been known, no need to be analyzed.
    public static List<String> no_analyzed_classes = new ArrayList<>();
    public static List<String> no_analyzed_methods = new ArrayList<>();
    
    //Log files
    public static final String using_methods = "logs/using/using_methods.txt";
    public static final String method_data = "logs/using/method_data.txt";
    public static final String analysis_data = "logs/using/analysis_data.txt";

    public static final String suspicious_methods = "logs/using/suspicious_methods.txt";
 

    // Judge whether the condition is met.
    // Replace the Value with its concrete assignment.
    // Sort the list according to the Value name's length first in case that one value name is the prefix of another Value name.

    public static boolean isInterestedUnit(Unit unit, List<Value> entry_value_copies){
        if(unit instanceof AssignStmt){
            AssignStmt as =(AssignStmt) unit;
            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- the entry value appears in the right of the Assignment unit.
            if(!Utils.hasRightValueOfAssignStmt(as, entry_value_copies).isEmpty()) {
                // Filter some uninterested types.
                if(Utils.hasCopyOfValues(as, entry_value_copies)){
                    return false;
                }
                if (!Utils.hasParameterOfInvokeStmt(ie, entry_value_copies).isEmpty()) {
                    SootMethod method = ie.getMethod();
                    String method_name = method.getName();
                    if(canFilterForTaintedParameter(base, method, method_name)){
                        return false;
                    }
                }
                return true;
            }
        } else if (unit instanceof InvokeStmt) {
            InvokeExpr ie = ((InvokeStmt) unit).getInvokeExpr();
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- Pass in the entry value as a parameter.
            if(!Utils.hasParameterOfInvokeStmt(ie, entry_value_copies).isEmpty()) {
                SootMethod method = ie.getMethod();
                String method_name = method.getName();
                if(canFilterForTaintedParameter(base, method, method_name)){
                    return false;
                }
                return true;
            }
        }
        return false;
    }

    // Treat the tainted / entry value as a whole, ignore the part (ie., the attribution) of it.
    public static boolean canFilterForTaintedBase(String base_type, String method_name){
        if(method_name.startsWith("remove")){
            return true;
        }
        return false;
    }

    public static boolean canFilterForTaintedParameter(Value base, SootMethod method, String method_name){
        String declaring_class;
        if (base != null) {
            declaring_class = ((RefType) base.getType()).getSootClass().getName();
        } else {
            declaring_class = method.getDeclaringClass().getName();
        }
        if (skip_methods.contains(method_name) || skip_classes.contains(declaring_class)) {
            return true;
        }
        if (method_name.startsWith("remove")) {
            return true;
        }
        if(base!=null && method_name.startsWith("get")){
            return true;
        }
        return false;
    }

    public static boolean needRecordMethod(int assignStmt, String callee_name){
        if(assignStmt == 1){
            if (callee_name.startsWith("add") && !callee_name.equals("add")){
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

    public static String getLikelyField(AssignStmt as){
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(ie==null && as.getUseBoxes().size()==2){
            String right_op = as.getRightOp().toString();
            if(right_op.contains(".<")){
                String likely_field = "<" + right_op.split(".<")[1];
                return likely_field;
            }
        }
        return null;
    }

    public static void updateTaintedValues(Value newly_tainted_value, List<Value> involved_tainted_values, List<Value> tainted_values, Map<Value, Value> newValueToCopy){
        // Update the tainted value.
        if(!involved_tainted_values.isEmpty()) {
            // Remove the previously tainted value.
            for(Value v : involved_tainted_values) {
                removePreviouslyTaintedValue(v, tainted_values, newValueToCopy);
            }
        }
        // Add the newly tainted value.
        addNewlyTaintedValue(newly_tainted_value, tainted_values, newValueToCopy);
        Log.logData(analysis_data, "--- Update the tainted value: " + tainted_values);
    }

    // associated element: related to the current analyzed method and its parents.
    public static void storeMethodAndElementAndCorrespondingDataStructure(SootMethod method, String element, String data_structure) {
        Pair m_e = new Pair<SootMethod, String>(method, element);

        Set<String> structures = methodAndElementToDataStructures.get(data_structure);
        if (structures == null) { // This key does not exist.
            structures = new HashSet<>();
            structures.add(data_structure);
            methodAndElementToDataStructures.put(m_e, structures);
        } else {
            structures.add(data_structure);
        }
    }

    public static void storeUsefulInfo(Unit unit, List<Value> entry_value_copies, Map<Value, Value> newValeToCopy, Map<Value, String> numericValueToConcreteAssignment){
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
            storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment);
        }
    }

    public static Block findStartBlock(CompleteBlockGraph cbg, Tainted entry, List<Value> entry_value_copies, Map<Value, Value> newValueToCopy,
                                       Map<Value, String> numericValueToConcreteAssignment){
        if(cbg==null || entry_value_copies == null) return null;

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
                if(isInterestedUnit(unit, entry_value_copies)){
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
                        if(isInterestedUnit(u, entry_value_copies)){
                            System.out.println("Interested unit: " + unit);
                            entry.setStartUnit(unit);
                            start_block = block;
                            break;
                        }
                    }
                    if(start_block!=null) break;
                }
                // Store some information before we skip the unit.
                storeUsefulInfo(unit, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment);
            }
            if(start_block != null) break;
        }
        return start_block;
    }

    public static Map<String, String> getEntries(){
        // Data preprocess.
        List<String> d_es = Log.readData(AnalysisForParsingClass.suspicious_structures);
        Map<String, Set<String>> suspiciousFiledToElements = new HashMap<>();
        for(String d_e : d_es){
            String structure = d_e.split("=>")[0];
            String element = d_e.split("=>")[1];
            String f = "<" + structure.split(".<")[1];
            Set<String> elements = suspiciousFiledToElements.get(f);
            if(elements == null){
                elements  = new HashSet<>();
                elements.add(element);
                suspiciousFiledToElements.put(f, elements);
            } else {
                elements.add(element);
            }
        }
        /*for(Map.Entry<String, Set<String>> entry : suspiciousFiledToElements.entrySet()){
            System.out.println(entry);
        }*/

        String className = AnalysisForParsingClass.parsedPackage_settings_class; // The class for storing the parsed package's settings.
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        // Get the public fields of the class.
        List<String> public_fields = new ArrayList<>();
        for(SootField f : cls.getFields()){
            if(f.isPublic()){
                public_fields.add(f.getSignature());
            }
        }
        // Find the entries for accessing the suspicious data structures.
        Map<String, String> entryToElement = new HashMap<>();
        for(String f : suspiciousFiledToElements.keySet()){
            if(public_fields.contains(f)){ // The public field can be accessed through the corresponding class object.
                entryToElement.put(f, suspiciousFiledToElements.get(f).toString());
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
                        String likely_field = getLikelyField(as);
                        if(likely_field!=null){
                            if (suspiciousFiledToElements.keySet().contains(likely_field)) {
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
                            entryToElement.put(method.getSignature(), suspiciousFiledToElements.get(field).toString());
                        }
                    }
                }
            }
        }
        return entryToElement;
    }

    public static void findEntryPoints(Map<String, String> entryToElement){
        for(SootClass cls : Scene.v().getClasses()) {
            try {
                if (!cls.getPackageName().contains("android")) continue; // Non Android package.
                if (cls.isInterface()) continue;
                List<SootMethod> methods = cls.getMethods();
                if(methods.isEmpty()){
                    continue;
                }
                for (int i = 0; i< methods.size(); i++) {
                    SootMethod method = methods.get(i);
                    if (!method.isConcrete()) continue;
                    Body body = method.retrieveActiveBody();
                    Tainted entry_point = new Tainted(method);
                    List<Value> entry_values = new ArrayList<>();
                    Set<String> entry_elements = new HashSet<>();
                    for (Unit unit : body.getUnits()) {
                        Value entry_value = null;
                        String entry_element = null;
                        if (unit instanceof IdentityStmt) {
                            IdentityStmt is = (IdentityStmt) unit;
                            storeParameterOfTaintedPoint(entry_point, is);
                        } else if (unit instanceof AssignStmt) {
                            AssignStmt as = (AssignStmt) unit;
                            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                            String likely_field = getLikelyField(as);
                            if (likely_field != null) {
                                if (entryToElement.keySet().contains(likely_field)) {
                                    entry_value = as.getLeftOp();
                                    entry_element = entryToElement.get(likely_field);
                                }
                            } else if (ie != null) {
                                SootMethod callee = ie.getMethod();
                                if (callee.isConcrete()) {
                                    String callee_sig = callee.getSignature();
                                    if (entryToElement.keySet().contains(callee_sig)) {
                                        entry_value = as.getLeftOp();
                                        entry_element = entryToElement.get(callee_sig);
                                    }
                                } else if (ie instanceof InterfaceInvokeExpr) {
                                    String callee_subSig = callee.getSubSignature();
                                    for (String entry : entryToElement.keySet()) {
                                        if (entry.contains(callee_subSig)) {
                                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                                            SootMethod implemented_method = Analysis.getImplementedMethodOfAbstractMethod(null, ifi, entry_point);
                                            if (implemented_method != null && implemented_method.getSignature().equals(entry)) {
                                                entry_value = as.getLeftOp();
                                                entry_element = entryToElement.get(entry);
                                                break;
                                            } else if (implemented_method == null) {
                                                System.out.println(method);
                                                exit(0);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if (entry_value != null) {
                            if (!entry_values.contains(entry_value)) {
                                entry_values.add(entry_value);
                            }
                            entry_elements.add(entry_element);
                        }
                    }
                    if (!entry_values.isEmpty()) {
                        Log.logData(using_methods, Utils.generatePartingLine("="));
                        Log.logData(using_methods, "+Method: " + method.getSignature());
                        Log.logData(using_methods, "+Entry value: " + entry_values);
                        entry_point.setTaintedValues(entry_values);
                        entry_point.setOuterElement(entry_elements.toString());
                        tainted_points.offer(entry_point);
                    }
                }
            } catch (Exception e) {
                System.out.println(cls);
                e.printStackTrace();
            }
        }
    }
    public static void dataFlowAnalysisForBlocks(List<Block> blocks, List<Integer> block_ids, Tainted entry, List<Value> entry_value_copies,
                                                 Map<Value, Value> newValueToCopy, Map<Value, String> numericValueToConcreteAssignment,
                                                 List<String> recorded_tainted_points) {
        SootMethod entry_method = entry.getMethod();
        String entry_element = entry.getOuterElement();
        Unit start_unit = entry.getStartUnit();
        List<Tainted> entry_parents = entry.getParents();

        // Copy the map.
        // Specific to this path.
        Map<Value, String> numericValueToConcreteAssignment_path = Utils.deepCopy(numericValueToConcreteAssignment);
        List<Value> entry_values_path = Utils.deepCopy(entry_value_copies);

        Value case_value = null; // The bridge value between two LookupSwithStmts.
        String data_structure = null;

        List<Value> tainted_values = new ArrayList<>();
        Unit tainted_unit = null;
        Map<Value, String> mapValueToTaintedItem =  new HashMap<>();

        for (int i = 0; i< block_ids.size(); i++) {
            int block_id = block_ids.get(i);
            Block block = blocks.get(block_id);
            int flag_start = 0;
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
                int flag_attribution = 0;
                List<Value> involved_entry_values = new ArrayList<>(); // The entry values that this unit contains.
                List<Value> involved_tainted_values = new ArrayList<>(); // The tainted values that this unit contains.

                if(unit instanceof TableSwitchStmt){
                    Utils.printPartingLine("!");
                    System.out.println("TableSwitchStmt: " + unit);
                    Utils.printPartingLine("!");
                    exit(0);
                }
                // Store useful information from this unit.
                storeUsefulInfo(unit, entry_values_path, newValueToCopy, numericValueToConcreteAssignment_path);

                // Filter wrong paths.
                if (unit instanceof LookupSwitchStmt) {
                    LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                    if (case_value == null) { // Get the bridge case value between two LookupSwitchStmts.
                        case_value = getCaseValue(lss);
                    }else if (lss.getKey().equals(case_value)) {
                        boolean wrong_path = isWrongPathForSwitchStmt(analysis_data, blocks, block_ids, i, lss, case_value, numericValueToConcreteAssignment_path);
                        if(wrong_path){
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
                    if(wrong_path){
                        Utils.generatePartingLine("!");
                        Log.logData(analysis_data, "Wrong path, stop analyzing!");
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
                                entry.storeDataStructure(data_structure);
                                storeMethodAndElementAndCorrespondingDataStructure(entry_method, entry_element, data_structure);
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
                // Focus on the entry / tainted value and its attributions.
                // If the tainted / entry value is passed in the callee, this callee is tainted.
                Set<Integer> tainted_param_indices = new HashSet<>();
                if (!involved_entry_values.isEmpty()) {
                    for (Value v : involved_entry_values) {
                        Integer param_index = Utils.isParameterOfInvokeStmt(ie, v);
                        if (param_index != -1) {
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if (!involved_tainted_values.isEmpty()) {
                    for (Value v : involved_tainted_values) {
                        Integer param_index = Utils.isParameterOfInvokeStmt(ie, v);
                        if (param_index != -1) {
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if (!tainted_param_indices.isEmpty()) {
                    Log.logData(analysis_data, "--- Tainted callee.");
                    if (canFilterForTaintedParameter(base, callee, callee_name)) {
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    if (callee.isConstructor()) {
                        if (base != null) {
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy);
                            tainted_unit = unit;
                            continue;
                        }
                    }
                    if (callee_name.equals("add") || callee_name.equals("put")) { // xxx.add(tainted_value)
                        if (base != null) {
                            if(base.getType().toString().contains("Map")){
                                String tainted_item = confirmTaintedItemOfMap(callee_name, tainted_param_indices);
                                storeMapValueAndCorrespondingTaintedItem(base, tainted_item, mapValueToTaintedItem, newValueToCopy);
                            }
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy);
                            tainted_unit = unit;
                            continue;
                        } else if(assignStmt == 1){
                            AssignStmt as = (AssignStmt) unit;
                            if(as.getLeftOp().getType().toString().contains("Map")){
                                String tainted_item = confirmTaintedItemOfMap(callee_name, tainted_param_indices);
                                storeMapValueAndCorrespondingTaintedItem(as.getLeftOp(), tainted_item, mapValueToTaintedItem, newValueToCopy);
                            }
                        }
                    }
                    if (callee_name.equals("arraycopy")) {
                        // Update the tainted value.
                        Value newly_tainted_value = ie.getArg(2);
                        updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy);
                        tainted_unit = unit;
                        continue;
                    }
                    if(callee_name.startsWith("get")){ // Obtain the attribute of the value.
                        flag_attribution = 1;
                    }
                    if (needRecordMethod(assignStmt, callee_name)) {
                        if (ie instanceof InterfaceInvokeExpr) { // Invoke an abstract method, try to get its body.
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                            callee = getImplementedMethodOfAbstractMethod(analysis_data, ifi, entry);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                        }
                        List<Value> tainted_parameters = new ArrayList<>();
                        for (int param_index : tainted_param_indices) {
                            Value parameter = Utils.getParameterOfMethod(callee, param_index);
                            if (parameter != null) {
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
                        String tainted_point_sig = callee.hashCode() + tainted_parameters.hashCode() + "";
                        if (!recorded_tainted_points.contains(tainted_point_sig)) { // This tainted point has not been stored.
                            Log.logData(analysis_data, "--- Record the tainted method: " + callee_name);
                            recorded_tainted_points.add(tainted_point_sig);
                            entry.storeTaintedChildren(new Tainted(callee, tainted_parameters, unit));
                            List<Tainted> parents = Utils.deepCopy(entry_parents);
                            parents.add(entry);
                            tainted_points.offer(new Tainted(callee, tainted_parameters, entry_element, parents, unit));
                        } else {
                            Log.logData(analysis_data, "--- This tainted method has been recoded.");
                        }
                    }
                } else {
                    if (base != null) {
                        if (tainted_values.contains(base) || entry_values_path.contains(base)) {
                            Log.logData(analysis_data, "--- Tainted base.");
                            String base_type = base.getType().toString();
                            if(canFilterForTaintedBase(base_type, callee_name)){
                                Log.logData(analysis_data, "--- Pass.");
                                continue;
                            }
                            if (callee_name.equals("get")) { // Obtain the attribution of this value.
                                flag_attribution = 1;
                            }
                        }
                    }
                }

                // Update the tainted value.
                if (assignStmt == 1) {
                    AssignStmt as = (AssignStmt) unit;
                    // There is a copy of entry value.
                    if(Utils.hasCopyOfValues(as, entry_values_path)){
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    if (ie == null && as.getUseBoxes().size() == 2) {
                        if(as.getRightOp().toString().contains(".<")){ // Obtain the attribution of the value.
                            flag_attribution = 1;
                        }
                    }
                    // Update the Map value information.
                    if(ie == null && as.getLeftOp().getType().toString().contains("Map") && mapValueToTaintedItem.containsKey(as.getRightOp())){
                        String tainted_item = mapValueToTaintedItem.get(as.getRightOp());
                        storeMapValueAndCorrespondingTaintedItem(as.getLeftOp(), tainted_item, mapValueToTaintedItem, newValueToCopy);
                    }
                    // Update the tainted value.
                    Value newly_tainted_value = as.getLeftOp();
                    if(flag_attribution == 1){
                        addNewlyTaintedValue(newly_tainted_value, tainted_values, newValueToCopy);
                    } else {
                        updateTaintedValues(newly_tainted_value, involved_tainted_values, tainted_values, newValueToCopy);
                    }
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
            entry.storeDataStructure(data_structure);
            storeMethodAndElementAndCorrespondingDataStructure(entry_method, entry_element, data_structure);
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

        Map<Value, String> numericValueToConcreteAssignment = new HashMap<Value, String>(); // The concrete value of all numeric Values (iX, bX, zX).
        Map<Value, Value> newValueToCopy = new HashMap<Value, Value>(); // The newly constructed object and its copy.

        List<Value> entry_value_copies = Utils.deepCopy(entry.getTaintedValues());

        // To avoid path explosion caused by massive blocks, we start our analysis with the block we are interested in.
        // Because we ignore some blocks directly, we need save some useful information from them.
        System.out.println("Find start block...");
        Block start_block = findStartBlock(cbg, entry, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment);
        if(start_block == null){
            entry.storeDataStructure(null);
            entry.storeTaintedChildren(null);
            Log.logData(analysis_data, "This method does not need to be analyzed.");
            Utils.printPartingLine("!");
            System.out.println("Cannot find the start block.");
            Utils.printPartingLine("!");
            return;
        }

        System.out.println("+ Start block id: " + start_block.getIndexInMethod());
        System.out.println("+ numeric: " + numericValueToConcreteAssignment);

        // Log data.
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
        /*if(total_num > 50000){
            System.out.println("To many paths.");
            Log.logData(analysis_data, "Path number > 50000, change.");
            Graph.paths.clear();
            List<Integer> path = new ArrayList<>();
            for (int i = start_block.getIndexInMethod(); i < cbg.getBlocks().size(); i++) {
                path.add(i);
            }
            Graph.paths.add(path);
        }*/

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
                    numericValueToConcreteAssignment, recorded_tainted_points);
            path_num+=1;
            if(path_num == total_num || path_num % 1000 == 0) {
                System.out.println("Analyzed path num: " + path_num);
            }

            //Utils.pause();
        }
    }

    public static void findSuspiciousMethods(){
        Log.deleteData(method_data);
        Log.deleteData(analysis_data);
        Log.deleteData(using_methods);
        //Log.deleteData(suspicious_structures);

        String[] skip_mds = {"append", "size"};
        String[] skip_cls = {"com.android.internal.util.AnnotationValidations", "android.util.Slog"};
        skip_methods.addAll(new ArrayList<>(Arrays.asList(skip_mds)));
        skip_classes.addAll(new ArrayList<>(Arrays.asList(skip_cls)));

        System.out.println("Find entry points...");
        Map<String, String> entryToElement = getEntries();
        findEntryPoints(entryToElement);
        Utils.pause();

        List<Tainted> analyzed_tainted_points = new ArrayList<>();

        while (!tainted_points.isEmpty()) {
            Tainted tainted_point = tainted_points.poll();
            SootMethod tainted_method = tainted_point.getMethod();
            String tainted_element = tainted_point.getOuterElement();
            List<Value> tainted_values = tainted_point.getTaintedValues();
            int flag_analyzed = 0;

            for (Tainted atp : analyzed_tainted_points) {
                if (atp.getMethod().equals(tainted_method) && atp.getTaintedValues().equals(tainted_values)) {
                    flag_analyzed = 1; // This tainted method has been analyzed.
                    tainted_point.setParameters(atp.getParameters()); // The same tainted methods have the same parameters.
                    List<String> structures = atp.getDataStructures();
                    tainted_point.setDataStructures(structures); // The same tainted methods have the same data structures.
                    if (structures != null) {
                        for (String structure : structures) {
                            storeMethodAndElementAndCorrespondingDataStructure(tainted_method, tainted_element, structure);
                        }
                    }
                    // If this method tainted other methods, store their information.
                    Set<Tainted> children = atp.getTaintedChildren();
                    tainted_point.setTaintedChildren(children); // The same tainted methods have the same tainted children.
                    if (children != null) {
                        List<Tainted> parents = Utils.deepCopy(tainted_point.getParents());
                        parents.add(tainted_point);
                        for (Tainted child : children) {
                            tainted_points.offer(new Tainted(child.getMethod(), child.getTaintedValues(), tainted_element, parents, child.getCallUnit()));
                        }
                    }
                    break;
                }
            }

            if (flag_analyzed == 1) {
                analyzed_tainted_points.add(tainted_point);
                continue;
            }

            Log.logData(analysis_data, Utils.generatePartingLine("#"));
            Log.logData(analysis_data, "+ Analyzed method: " + tainted_method);
            Log.logData(analysis_data, "+ Entry value: " + tainted_point.getTaintedValues());
            analyzed_tainted_points.add(tainted_point);
            dataFlowAnalysisForMethod(tainted_point);

            //Utils.pause();
        }
    }

    public static void test(SootClass cls, Map<String, String> entryToElement){
        List<SootMethod> methods = cls.getMethods();
        for (int i = 0; i < methods.size(); i++) {
            SootMethod method = methods.get(i);
            if (!method.isConcrete()) continue;
            Body body = method.retrieveActiveBody();
            Tainted entry_point = new Tainted(method);
            List<Value> entry_values = new ArrayList<>();
            Set<String> entry_elements = new HashSet<>();
            for (Unit unit : body.getUnits()) {
                Value entry_value = null;
                String entry_element = null;
                if (unit instanceof IdentityStmt) {
                    IdentityStmt is = (IdentityStmt) unit;
                    storeParameterOfTaintedPoint(entry_point, is);
                } else if (unit instanceof AssignStmt) {
                    AssignStmt as = (AssignStmt) unit;
                    InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                    String likely_field = getLikelyField(as);
                    if (likely_field != null) {
                        if (entryToElement.keySet().contains(likely_field)) {
                            entry_value = as.getLeftOp();
                            entry_element = entryToElement.get(likely_field);
                        }
                    } else if (ie != null) {
                        SootMethod callee = ie.getMethod();
                        if (callee.isConcrete()) {
                            String callee_sig = callee.getSignature();
                            if (entryToElement.keySet().contains(callee_sig)) {
                                entry_value = as.getLeftOp();
                                entry_element = entryToElement.get(callee_sig);
                            }
                        } else if (ie instanceof InterfaceInvokeExpr) {
                            String callee_subSig = callee.getSubSignature();
                            for (String entry : entryToElement.keySet()) {
                                if (entry.contains(callee_subSig)) {
                                    InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                                    SootMethod implemented_method = Analysis.getImplementedMethodOfAbstractMethod(null, ifi, entry_point);
                                    if (implemented_method != null && implemented_method.getSignature().equals(entry)) {
                                        entry_value = as.getLeftOp();
                                        entry_element = entryToElement.get(entry);
                                        break;
                                    } else if (implemented_method == null) {
                                        System.out.println(method);
                                        exit(0);
                                    }
                                }
                            }
                        }
                    }
                }
                if (entry_value != null) {
                    if (!entry_values.contains(entry_value)) {
                        entry_values.add(entry_value);
                    }
                    entry_elements.add(entry_element);
                }
            }
            if (!entry_values.isEmpty()) {
                Log.logData(using_methods, Utils.generatePartingLine("="));
                Log.logData(using_methods, "+Method: " + method.getSignature());
                Log.logData(using_methods, "+Entry value: " + entry_values);
                entry_point.setTaintedValues(entry_values);
                entry_point.setOuterElement(entry_elements.toString());
                tainted_points.offer(entry_point);
            }
        }
    }
}
