package analysis;

import comparator.StringComparator;
import graph.Graph;
import soot.*;
import soot.jimple.*;
import soot.jimple.spark.ondemand.pautil.SootUtil;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.scalar.Pair;

import java.util.*;

import static java.lang.System.exit;

public class AnalysisForUsingMethods extends Analysis{

    // The tainted_methods needed to be analysed.
    // Each object consists of <tainted method, tainted value, associated element>
    // Use queue to do BFS.
    public static Queue<Tainted> tainted_points = new LinkedList<Tainted>();

    // method c=> data structures.
    public static Map<SootMethod, Set<String>> methodToDataStructures = new HashMap<SootMethod, Set<String>>();

    // skip_names: important names. These names are unlikely an element name.
    public static List<String> skip_names = new ArrayList<>();

    // skip_methods, skip_classes: important methods / classes. If a statement contains this kind of methods / classes, just skipping this statement.
    public static List<String> skip_methods = new ArrayList<>();
    public static List<String> skip_classes = new ArrayList<>();

    // no_analyzed_methods, no_analyzed_classes: these methods' / classes' functions have been known, no need to be analyzed.
    public static List<String> no_analyzed_classes = new ArrayList<>();
    public static List<String> no_analyzed_methods = new ArrayList<>();

    // Our analysis is path-sensitive. We analyze each path of a method's block graph.
    // But some methods is unsuitable for path-sensitive 
    // In general, these methods contains many If statements,
    // and will generate lots of redundant paths.
    public static List<String> path_insensitive_methods = new ArrayList<>();
    
    //Log files
    public static final String entry_bridges = "logs/using/entry_bridges.txt";
    public static final String using_methods = "logs/using/using_methods.txt";
    // Analysis.
    public static final String method_data = "logs/using/method_data.txt";
    public static final String analysis_data = "logs/using/analysis_data.txt";
    // Results.
    public static final String suspicious_methods = "logs/using/suspicious_methods.txt";
    public static final String suspicious_methods_final = "logs/using/suspicious_methods_deduplicate.txt";
    public static final String using_method_structs = "logs/using/using_method_structs.txt";
 

    public static boolean isDeDuplicateMethod(String element){
        List<String> element_list = Arrays.asList(element.split(","));
        int element_size = element_list.size();
        for(String e : element_list){
            if(e.contains("library") || e.contains("uses-permission")){
                element_size -= 1;
            }
        }
        if(element_size > 0){
            return false;
        } else {
            System.out.println("=== Deduplicate.");
            return true;
        }
    }

    public static boolean isInterestedUnit(Unit unit, List<Value> entry_value_copies){
        if(unit instanceof AssignStmt){
            AssignStmt as =(AssignStmt) unit;
            // Interested unit -- the entry value appears in the right of the Assignment unit.
            if(!Utils.hasRightValuesOfAssignStmt(as, entry_value_copies).isEmpty()) {
                // Filter some uninterested types.
                if(Utils.hasCopyOfValues(as, entry_value_copies)){
                    return false;
                }
                return true;
            }
        } else if (unit instanceof InvokeStmt) {
            InvokeExpr ie = ((InvokeStmt) unit).getInvokeExpr();
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- pass in the entry value as a parameter.
            if(!Utils.hasParametersOfInvokeExpr(ie, entry_value_copies).isEmpty()) {
                return true;
            }
            // Interested unit -- the entry value is the base of the method toArray.
            if(entry_value_copies.contains(base)){
                String method_name = ie.getMethod().getName();
                if(method_name.equals("toArray")){
                    return true;
                }
            }
        }
        return false;
    }

    public static int isTaintedAttribute(String method_name, Value base, Set<Integer> involved_tainted_attributes){
        if(method_name.startsWith("get")){
            //System.out.println("=== " + ie);
            if (base == null && !involved_tainted_attributes.isEmpty()) {
                return 2;
            }
            return 1;
        }
        return -1;
    }
    public static int isTaintedAttribute(Value base, String method_name, Set<Value> tainted_attributes){
        if(base != null){
            // $r6 = virtualinvoke r4.<android.content.pm.parsing.component.ParsedProvider: java.lang.String getAuthority()>()
            // $r7 = virtualinvoke $r6.<java.lang.String: java.lang.String[] split(java.lang.String)>(";")
            if(method_name.startsWith("get") || method_name.startsWith("next") ||
                    "split_substring_indexOf_values_keySet_entrySet_iterator".contains(method_name)){
                if(tainted_attributes.contains(base)) {
                    return 2;
                }
                return 1;
            }
        }
        return -1;
    }

    public static int isTaintedAttribute(AssignStmt as, Set<Value> tainted_attributes){
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
            if (tainted_attributes.contains(likely_attribute)) {
                return 2;
            }
            return 1;
        }
        return -1;
    }

    public static boolean isSuspiciousMethod(Set<String> structures, List<Tainted> analyzed_tainted_point){
        List<String> structures_new = new ArrayList<>(structures);
        List<String> structures_old = new ArrayList<>(structures);
        for (String s: structures_old){
            String s_old = s;
            int flag_remove = 0;
            if(s==null){
                structures.remove(null);
                flag_remove = 1;
            } else if (s.contains("remove") || s.contains("return") || s.startsWith("<")){
                continue;
            } else if (s.contains("attribute") || s.endsWith("Exception")){
                flag_remove = 1;
            } else {
                if (s.contains("unknown")) {
                    s = transformUnknownTaintedMapItem(s, analyzed_tainted_point);
                }
                String type = s.split("_")[0];
                if (type.endsWith("List") || type.endsWith("[]") || type.endsWith("Stack") || type.endsWith("Queue") ||
                        type.endsWith("Collection") || type.endsWith("Iterator") || type.endsWith("Map&Entry") ||
                        type.endsWith("StringBuilder")) {
                    flag_remove = 1;
                } else if (type.endsWith("Map") || type.endsWith("SparseArray")) {
                    if (!s.contains("_key")) {
                        flag_remove = 1;
                    }
                }
            }
            if(flag_remove == 1){
                structures_new.remove(s_old);
            }
        }
        System.out.println("=== Processed data structures: " + structures_new);
        if(structures_new.isEmpty()){
            return false;
        } else {
            return true;
        }
    }

    public static boolean canFilterForTaintedBase(Value base, String method_name){
        String base_type = base.getType().toString();
        String declaring_class = ((RefType) base.getType()).getSootClass().getName();

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

    public static boolean needRecordMethod(int assignStmt, SootMethod method, Value base, Unit unit){
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
            if(Utils.isMapValue(as.getLeftOp())){
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

    public static void getInvolvedTaintedObjectsFromTaintedParams(InvokeExpr ie, Set<Integer> tainted_param_indices, Map<Value, String> taintedMapValueToTaintedItem,
                                                                  Set<Value> tainted_attributes, Map<Integer, String> involved_tainted_mapItems,
                                                                  Set<Integer> involved_tainted_attributes){
        for (int param_index : tainted_param_indices) {
            Value tainted_param = ie.getArg(param_index);
            if(Utils.isMapValue(tainted_param)){
                String tainted_map_item = taintedMapValueToTaintedItem.get(tainted_param);
                if(tainted_map_item!=null) {
                    involved_tainted_mapItems.put(param_index, tainted_map_item);
                } else {
                    Utils.printPartingLine("!");
                    System.out.println("Cannot find the tainted item of the Map value: " + tainted_param);
                    Utils.printPartingLine("!");
                    exit(0);
                }
            }
            if(tainted_attributes.contains(tainted_param)){
                involved_tainted_attributes.add(param_index);
            }
        }
    }

    public static Value getInvolvedRemovedStruct(int assignStmt, Value base, String callee_name, Unit unit){
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
    public static Map<String, String> getEntryBridges(){
        // Data preprocess.
        List<String> d_es = Log.readData(AnalysisForParsingClass2.suspicious_structures);
        Map<String, Set<String>> suspiciousStructureToElements = new HashMap<>();
        for(String d_e : d_es){
            String structure = d_e.split("=>")[0].split("_")[0];
            String element = d_e.split("=>")[1];
            Set<String> elements = suspiciousStructureToElements.get(structure);
            if(elements == null){
                elements  = new HashSet<>();
                elements.add(element);
                suspiciousStructureToElements.put(structure, elements);
            } else {
                elements.add(element);
            }
        }
       /* for(Map.Entry<String, Set<String>> entry : suspiciousFiledToElements.entrySet()){
            System.out.println(entry);
        }
        Utils.pause();*/
        String className = AnalysisForParsingClass.parsedPackage_settings_class; // The class for storing the parsed package's settings.
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        // Get the public fields of the class.
        List<String> public_fields = new ArrayList<>();
        for(SootField f : cls.getFields()){
            if(f.isPublic()){
                public_fields.add(f.getSignature());
            }
        }
        // Find the entry bridges for accessing the suspicious data structures.
        Map<String, String> entryBridgeToElement = new HashMap<>();
        for(String f : suspiciousStructureToElements.keySet()){
            if(public_fields.contains(f)){ // The public field can be accessed through the corresponding class object.
                entryBridgeToElement.put(f, suspiciousStructureToElements.get(f).toString());
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
                        String likely_field = getField(as);
                        if(likely_field!=null){
                            if (suspiciousStructureToElements.keySet().contains(likely_field)) {
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
                            entryBridgeToElement.put(method.getSignature(), suspiciousStructureToElements.get(field).toString());
                        }
                    }
                }
            }
        }
        for(Map.Entry<String, String> entry : entryBridgeToElement.entrySet()){
            Log.logData(entry_bridges, entry.toString());
        }
        return entryBridgeToElement;
    }

    public static void storeMethodAndCorrespondingDataStructure(SootMethod method, String data_structure) {
        Set<String> structures = methodToDataStructures.get(method);
        if (structures == null) { // This key does not exist.
            structures = new HashSet<>();
            structures.add(data_structure);
            methodToDataStructures.put(method, structures);
        } else {
            structures.add(data_structure);
        }
    }

    public static void storeUsefulInfo(AssignStmt as, List<Value> entry_value_copies, Map<Value, Value> newValeToCopy,
                                       Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToField,
                                       Map<Value, String> mapValueToTaintedItem, Set<Value> tainted_entry_attributes){
        if(as==null) return;

        if (Utils.hasCopyOfValues(as, entry_value_copies)) {
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "--- Copy entry value: " + as);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Value copy = as.getLeftOp();
            if(!entry_value_copies.contains(copy)) {
                entry_value_copies.add(copy);
            }
            if(mapValueToTaintedItem.containsKey(as.getRightOp())){
                String tainted_map_item = mapValueToTaintedItem.get(as.getRightOp());
                storeTaintedMapValueAndCorrespondingTaintedItem(copy, tainted_map_item, mapValueToTaintedItem, newValeToCopy);
            }
            if(tainted_entry_attributes.contains(as.getRightOp())){
                tainted_entry_attributes.add(copy);
            }
        }
        storeNewValueAndCorrespondingCopy(as, newValeToCopy);
        storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment);
        storeValueAndCorrespondingField(as, valueToField);
    }

    public static void storeDataStructure(Value tainted_value, Tainted tainted_point, Map<Value, String> taintedMapValueToTaintedItem,
                                          Set<Value> tainted_attributes, Map<Value, String> valueToField,
                                          Value return_value, int flag_remove){
        String data_structure = getDataStructure(tainted_value, taintedMapValueToTaintedItem, valueToField, tainted_attributes,
                return_value, flag_remove);
        tainted_point.storeDataStructure(data_structure);
        // Find the tainted point's farthest ancestor.
        SootMethod farthest_ancestor = tainted_point.getMethod();
        List<Tainted> parents = tainted_point.getParents();
        if(parents!=null && !parents.isEmpty()) {
             farthest_ancestor = parents.get(0).getMethod();
        }
        storeMethodAndCorrespondingDataStructure(farthest_ancestor, data_structure);
    }

    public static String transformUnknownTaintedMapItem(String ds, List<Tainted> analyzed_tainted_points){
        String method_sig = ds.split("unknown\\(")[1].split(">")[0] + ">";
        int flag_known = 0;
        for(Tainted point : analyzed_tainted_points){
            //System.out.println("=== " + method_sig);
            if(point.getMethod().getSignature().equals(method_sig)){
                List<String> structures = point.getDataStructures();
                if(structures == null) {
                    continue;
                }
                List<String> maps = new ArrayList<>();
                for(String s : structures) {
                    if(s!=null && s.contains("_map")){
                        maps.add(s);
                    }
                }
                if(maps.isEmpty()){
                    continue;
                }
                Collections.sort(maps, new StringComparator());
                String bridge = maps.get(0);
                if(!maps.get(0).contains("return")){
                    for(String map : maps){
                        if(map.contains("return")){
                            bridge = map;
                            break;
                        }
                    }
                }
                String tainted_item = bridge.split("_map")[1];
                //System.out.println("==== " + tainted_item);
                if(tainted_item.contains("unknown")){
                    method_sig = tainted_item.split("unknown\\(")[1].split(">")[0] + ">";
                    continue;
                }
                ds = ds.split("_unknown")[0] + tainted_item;
                //System.out.println("===== " + ds);
                flag_known = 1;
            }
            if(flag_known == 1){
                break;
            }
        }
        return ds;
    }

    public static void updateTaintedValues(Value newly_tainted_value, List<Value> involved_tainted_values, List<Value> entry_values,
                                           List<Value> tainted_values, Map<Value, Value> newValueToCopy){
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
        // The entry value has been re-defined.
        if(entry_values.contains(newly_tainted_value)){
            entry_values.remove(newly_tainted_value);
            Log.logData(analysis_data, "--- Remove re-defined entry value: " + newly_tainted_value);
            Log.logData(analysis_data, "--- Update the entry value: " + entry_values);
        }
    }

    public static void updateTaintedAttributesFromEntry(int flag_attribute_entry, Value newly_tainted_value, Set<Value> tainted_entry_attributes){
        if(newly_tainted_value == null || tainted_entry_attributes == null) return;

        if(flag_attribute_entry == 1){
            tainted_entry_attributes.add(newly_tainted_value);
            Log.logData(analysis_data, "--- Update the tainted attribute: " + tainted_entry_attributes);
        } else if(tainted_entry_attributes.contains(newly_tainted_value)){ // This value is no longer an attribute.
            tainted_entry_attributes.remove(newly_tainted_value);
            Log.logData(analysis_data, "--- Remove the tainted attribute: " + newly_tainted_value);
            Log.logData(analysis_data, "--- Update the tainted attribute: " + tainted_entry_attributes);
        }
    }

    // Find the blocks that contains the interested units.
    public static List<Block> findAllInterestedBlocks(CompleteBlockGraph cbg, Tainted entry, List<Value> entry_value_copies, Set<AssignStmt> entry_assigns){
        List<Block> interested_blocks = new ArrayList<>();
        int store_param = entry.getParameters() == null? 1:0;
        for(Block block : cbg.getBlocks()){
            int flag_interested = 0;
            for(Unit unit : block){
                if(store_param == 1) {
                    if (unit instanceof IdentityStmt) {
                        IdentityStmt is = (IdentityStmt) unit;
                        storeParameterOfTaintedPoint(entry, is);
                        continue;
                    }
                }
                // If there exist entry assignments, the block containing the entry assignment is interested.
                // Otherwise, the block containing "interesting" unit is interested.
                if(entry_assigns != null){
                    if(unit instanceof AssignStmt){
                        AssignStmt as = (AssignStmt) unit;
                        if(entry_assigns.contains(as)){
                            flag_interested = 1;
                        }
                    } else if(unit instanceof SwitchStmt){
                        // For switch-case statement, we need to analyze each case.
                        SwitchStmt ss = (SwitchStmt) unit;
                        for (int i = 0; i < ss.getTargets().size(); i++) {
                            Unit u = ss.getTarget(i);
                            if (entry_assigns != null) {
                                if (u instanceof AssignStmt) {
                                    AssignStmt as = (AssignStmt) u;
                                    if (entry_assigns.contains(as)) {
                                        flag_interested = 1;
                                    }
                                }
                            }
                            if(flag_interested == 1){
                                break;
                            }
                        }
                    }
                }else {
                    if(isInterestedUnit(unit, entry_value_copies)){
                        flag_interested = 1;
                    }else if(unit instanceof SwitchStmt){
                        // For switch-case statement, we need to analyze each case.
                        SwitchStmt ss = (SwitchStmt) unit;
                        for (int i = 0; i < ss.getTargets().size(); i++) {
                            Unit u = ss.getTarget(i);
                            if(isInterestedUnit(u, entry_value_copies)) {
                                flag_interested = 1;
                            }
                            if(flag_interested == 1){
                                break;
                            }
                        }
                    }
                }
                if(flag_interested == 1){
                    if(!interested_blocks.contains(block)){
                        interested_blocks.add(block);
                    }
                    break;
                }
            }
        }
        return interested_blocks;
    }

    // For path-sensitive analysis.
    // Find the LCA block of all interested blocks (including the block in the interested blocks) .
    public static Block findStartBlock(List<Block> interested_blocks, CompleteBlockGraph cbg, Tainted entry, List<Value> entry_value_copies,
                                       Map<Value, Value> newValueToCopy, Map<Value, String> numericValueToConcreteAssignment,
                                       Map<Value, String> valueToField, Map<Value, String> mapValueToTaintedItem,
                                       Set<Value> tainted_entry_attributes){
        if(interested_blocks.isEmpty()){
            return null;
        }
        int start_block_id;
        if(interested_blocks.size() == 1){
            start_block_id = interested_blocks.get(0).getIndexInMethod();
        } else {
            start_block_id = Graph.getLeastCommonAncestorOfBlocks2(interested_blocks);
            int start_block_id2 = Graph.getLeastCommonAncestorOfBlocks(interested_blocks);
            if(start_block_id2!=start_block_id){
                Utils.printPartingLine("!");
                System.out.println("--- Stupid: " + start_block_id);
                System.out.println("--- smart: " + start_block_id2);
                Utils.printPartingLine("!");
                exit(0);
            }
        }

        for(Block block : cbg.getBlocks()){
            if(block.getIndexInMethod() == start_block_id){
                return block;
            }
            for(Unit unit : block){
                // Store some information before we skip the unit.
                if(unit instanceof AssignStmt) {
                    AssignStmt as = (AssignStmt) unit;
                    storeUsefulInfo(as, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment,
                            valueToField, mapValueToTaintedItem, tainted_entry_attributes);
                }
            }
        }
        return null;
    }

    // For path-insensitive analysis.
    // Find the first interested block.
    public static Block findStartBlock(CompleteBlockGraph cbg, Tainted entry, List<Value> entry_value_copies, Map<Value, Value> newValueToCopy,
                                       Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToField,
                                       Map<Value, String> mapValueToTaintedItem, Set<Value> tainted_entry_attributes){
        if(cbg==null || entry_value_copies == null) return null;

        Block start_block = null;
        int store_param = entry.getParameters() == null? 1:0;
        int entry_assign = entry.getEntryAssigns() == null? 0:1;

        for(Block block : cbg.getBlocks()){
            for(Unit unit : block){
                if(store_param == 1) {
                    if (unit instanceof IdentityStmt) {
                        IdentityStmt is = (IdentityStmt) unit;
                        storeParameterOfTaintedPoint(entry, is);
                        continue;
                    }
                }
                // If this entry point has entry assignments, the analysis scope should under the first entry assignment.
                if(entry_assign == 1){
                    if(unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        if (entry.getEntryAssigns().contains(as)) {
                            System.out.println("Interested unit: " + unit);
                            entry.setStartUnit(as);
                            start_block = block;
                            break;
                        }
                    } else if(unit instanceof SwitchStmt){
                        // For switch-case statement, we need to analyze each case.
                        SwitchStmt ss = (SwitchStmt) unit;
                        for (int i = 0; i < ss.getTargets().size(); i++) {
                            Unit u = ss.getTarget(i);
                            if (u instanceof AssignStmt) {
                                AssignStmt as = (AssignStmt) u;
                                if (entry.getEntryAssigns().contains(as)) {
                                    System.out.println("Interested unit: " + unit);
                                    entry.setStartUnit(as);
                                    start_block = block;
                                    break;
                                }
                            }
                        }
                        if(start_block!=null) break;
                    }
                } else {
                    if (isInterestedUnit(unit, entry_value_copies)) {
                        System.out.println("Interested unit: " + unit);
                        entry.setStartUnit(unit);
                        start_block = block;
                        break;
                    }
                    if (unit instanceof SwitchStmt) {
                        // For switch-case statement, we need to analyze each case.
                        SwitchStmt ss = (SwitchStmt) unit;
                        for (int i = 0; i < ss.getTargets().size(); i++) {
                            Unit u = ss.getTarget(i);
                            if (isInterestedUnit(u, entry_value_copies)) {
                                System.out.println("Interested unit: " + unit);
                                entry.setStartUnit(unit);
                                start_block = block;
                                break;
                            }
                        }
                        if (start_block != null) break;
                    }
                }
                if(unit instanceof AssignStmt) {
                    AssignStmt as = (AssignStmt) unit;
                    // Store some information before we skip the unit.
                    storeUsefulInfo(as, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment,
                            valueToField, mapValueToTaintedItem, tainted_entry_attributes);
                }
            }
            if(start_block != null) break;
        }
        return start_block;
    }

    public static void findEntryPoints(Map<String, String> entryBridgeToElement, Map<SootMethod, String> use_methods){
        int method_num = 0;
        for(SootClass cls : Scene.v().getClasses()) {
            try {
                if (!cls.getPackageName().contains("android")) continue; // Non Android package.
                if (cls.isInterface()) continue;
                List<SootMethod> methods = cls.getMethods();
                if(methods.isEmpty()){
                    continue;
                }
                for (int i = 0; i< methods.size(); i++) {
                    method_num += 1;
                    SootMethod method = methods.get(i);
                    if (!method.isConcrete()) continue;
                    Body body = method.retrieveActiveBody();
                    Tainted entry_point = new Tainted(method);
                    List<Value> entry_values = new ArrayList<>();
                    Set<String> entry_elements = new HashSet<>();
                    Set<AssignStmt> entry_assigns = new HashSet<>();
                    for (Unit unit : body.getUnits()) {
                        Value entry_value = null;
                        String entry_element = null;
                        if (unit instanceof IdentityStmt) {
                            IdentityStmt is = (IdentityStmt) unit;
                            storeParameterOfTaintedPoint(entry_point, is);
                        } else if (unit instanceof AssignStmt) {
                            AssignStmt as = (AssignStmt) unit;
                            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                            String likely_field = getField(as);
                            if (likely_field != null) {
                                if (entryBridgeToElement.keySet().contains(likely_field)) {
                                    entry_value = as.getLeftOp();
                                    entry_element = entryBridgeToElement.get(likely_field);
                                }
                            } else if (ie != null) {
                                SootMethod callee = ie.getMethod();
                                if (callee.isConcrete()) {
                                    String callee_sig = callee.getSignature();
                                    if (entryBridgeToElement.keySet().contains(callee_sig)) {
                                        entry_value = as.getLeftOp();
                                        entry_element = entryBridgeToElement.get(callee_sig);
                                    }
                                } else if (ie instanceof InterfaceInvokeExpr) {
                                    String callee_subSig = callee.getSubSignature();
                                    for (String entry : entryBridgeToElement.keySet()) {
                                        if (entry.contains(callee_subSig)) {
                                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                                            SootMethod implemented_method = getImplementedMethodOfAbstractMethod(null, ifi, entry_point);
                                            if (implemented_method != null && implemented_method.getSignature().equals(entry)) {
                                                entry_value = as.getLeftOp();
                                                entry_element = entryBridgeToElement.get(entry);
                                                break;
                                            } else if (implemented_method == null) {
                                                System.out.println(method);
                                                exit(0);
                                            }
                                        }
                                    }
                                }
                            }
                            if (entry_value != null) {
                                if(!entry_values.contains(entry_value)) {
                                    entry_values.add(entry_value);
                                }
                                entry_elements.add(entry_element);
                                entry_assigns.add(as);
                            }
                        }
                    }
                    if (!entry_values.isEmpty()) {
                        Log.logData(using_methods, Utils.generatePartingLine("="));
                        Log.logData(using_methods, "+ Method: " + method.getSignature());
                        Log.logData(using_methods, "+ Entry value: " + entry_values);
                        entry_point.setTaintedValues(entry_values);
                        entry_point.setOuterElement(entry_elements.toString());
                        entry_point.setEntryAssigns(entry_assigns);
                        tainted_points.offer(entry_point);
                        use_methods.put(method, entry_elements.toString());
                    }
                }
            } catch (Exception e) {
                System.out.println(cls);
                e.printStackTrace();
            }
        }
        System.out.println("Total method number: " + method_num);
    }

    public static void findSuspiciousMethods(){
        Log.deleteData(using_methods);
        Log.deleteData(entry_bridges);

        Log.deleteData(method_data);
        Log.deleteData(analysis_data);

        Log.deleteData(using_method_structs);
        Log.deleteData(suspicious_methods);
        Log.deleteData(suspicious_methods_final);

        String[] skip_mds = {"isEmpty", "byteSizeOf", "size", "forEachPackage"};
        String[] skip_cls = {"com.android.internal.util.AnnotationValidations","java.io.PrintWriter", "android.os.AsyncTask"};
        String[] pims = {"generateWithoutComponentsUnchecked", "assertPackageIsValid", "preparePackageLI", "scanPackageOnlyLI",
                         "addPackageInternal", "restorePermissionState", "shouldGrantPermissionByProtectionFlags",
                         "grantRuntimePermissionInternal"}; // "setAllowlistedRestrictedPermissionsInternal"
        skip_methods.addAll(new ArrayList<>(Arrays.asList(skip_mds)));
        skip_classes.addAll(new ArrayList<>(Arrays.asList(skip_cls)));
        path_insensitive_methods.addAll(new ArrayList<>(Arrays.asList(pims)));


        System.out.println("Find entry points...");
        Map<String, String> entryBridgesToElement = getEntryBridges();
        Map<SootMethod, String> use_methods = new HashMap<>();
        findEntryPoints(entryBridgesToElement, use_methods);
        System.out.println("Done");
        Utils.printPartingLine("+");

        List<Tainted> analyzed_tainted_points = new ArrayList<>();

        while (!tainted_points.isEmpty()) {
            Tainted tainted_point = tainted_points.poll();
            SootMethod tainted_method = tainted_point.getMethod();
            String tainted_element = tainted_point.getOuterElement();
            Unit tainted_call_unit = tainted_point.getCallUnit();

            Log.logData(analysis_data, Utils.generatePartingLine("#"));
            Log.logData(analysis_data, "+ Analyzed method: " + tainted_method);
            if(tainted_method.getName().startsWith("dump")){
                Log.logData(analysis_data, "--- Pass.");
                Utils.printPartingLine("=");
                System.out.println("+ Method: " + tainted_method.getName());
                System.out.println("+ Pass.");
                continue;
            }

            // Confirm the implemented method when the tainted method is abstract.
            if(tainted_method.isAbstract()) {
                InvokeExpr ie = Utils.getInvokeOfUnit(tainted_call_unit);
                if (ie instanceof InterfaceInvokeExpr) { // Invoke an abstract method, try to get its body.
                    Log.logData(analysis_data, Utils.generatePartingLine("+"));
                    InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                    SootMethod implemented_method = getImplementedMethodOfAbstractMethod(analysis_data, ifi, tainted_point);
                    tainted_point.setMethod(implemented_method);
                    Log.logData(analysis_data, Utils.generatePartingLine("+"));
                }
            }

            String tainted_point_sig = generateTaintedPointSignature(tainted_point);
            int flag_analyzed = 0;
            for (Tainted atp : analyzed_tainted_points) {
                String atp_Sig = generateTaintedPointSignature(atp);
                if (atp_Sig.equals(tainted_point_sig)) {
                    Log.logData(analysis_data, "This method has been analyzed.");
                    Utils.printPartingLine("=");
                    System.out.println("+ Method: " + tainted_method.getName());
                    System.out.println("+ Analyzed.");
                    flag_analyzed = 1; // This tainted method has been analyzed.
                    tainted_point.setParameters(atp.getParameters()); // The same tainted methods have the same parameters.
                    List<String> structures = atp.getDataStructures();
                    tainted_point.setDataStructures(structures); // The same tainted methods have the same data structures.
                    if (structures != null) {
                        SootMethod farthest_ancestor = tainted_method;
                        List<Tainted> parents = tainted_point.getParents();
                        if(parents!=null && !parents.isEmpty()) {
                            farthest_ancestor = parents.get(0).getMethod();
                        }
                        for (String structure : structures) {
                            storeMethodAndCorrespondingDataStructure(farthest_ancestor, structure);
                        }
                    }
                    // If this method tainted other methods, store their information.
                    Set<Tainted> children = atp.getTaintedChildren();
                    tainted_point.setTaintedChildren(children); // The same tainted methods have the same tainted children.
                    if (children != null) {
                        List<Tainted> new_parents = Utils.deepCopy(tainted_point.getParents());
                        new_parents.add(tainted_point);
                        for (Tainted child : children) {
                            Tainted newly_tainted_point = new Tainted(child.getMethod(), child.getTaintedParamIndices(), tainted_element,
                                    new_parents, child.getCallUnit(), child.getTaintedMapItem());
                            newly_tainted_point.setTaintedAttributes(child.getTaintedAttributes());
                            tainted_points.offer(newly_tainted_point);
                        }
                    }
                    break;
                }
            }

            if (flag_analyzed == 1) {
                analyzed_tainted_points.add(tainted_point);
                continue;
            }

            analyzed_tainted_points.add(tainted_point);
            dataFlowAnalysisForMethod(tainted_point);

            //Utils.pause();
        }

        Utils.printPartingLine("#");
        System.out.println(use_methods.size());
        System.out.println(methodToDataStructures.size());

        int suspicious_method_num = 0;
        int suspicious_method_num_final = 0;
        for(Map.Entry<SootMethod, Set<String>> entry : methodToDataStructures.entrySet()){
            System.out.println(entry);

            SootMethod method = entry.getKey();
            String method_sig = method.getSignature();
            Set<String> structs = entry.getValue();
            String element = use_methods.get(method);
            System.out.println("=== Element: " + element);
            Log.logData(using_method_structs, Utils.generatePartingLine("#"));
            Log.logData(using_method_structs, "+ Method: " + method_sig);
            Log.logData(using_method_structs, Utils.generatePartingLine("-"));
            Log.logData(using_method_structs, "+ Element: " + element);

            int flag_suspicious = 0;
            int flag_suspicious_deduplicate = 1;
            if(isSuspiciousMethod(structs, analyzed_tainted_points)) {
                flag_suspicious = 1;
                suspicious_method_num += 1;
                Log.logData(suspicious_methods, Utils.generatePartingLine("#"));
                Log.logData(suspicious_methods, "+ Method: " + method_sig);
                Log.logData(suspicious_methods, Utils.generatePartingLine("-"));
                Log.logData(suspicious_methods, "+ Element: " + element);
                if (!isDeDuplicateMethod(element)) {
                    flag_suspicious_deduplicate = 0;
                    suspicious_method_num_final += 1;
                    Log.logData(suspicious_methods_final, Utils.generatePartingLine("#"));
                    Log.logData(suspicious_methods_final, "+ Method: " + method_sig);
                    Log.logData(suspicious_methods_final, Utils.generatePartingLine("-"));
                    Log.logData(suspicious_methods_final, "+ Element: " + element);
                }
            }
            for(String s : structs) {
                if (s != null && s.contains("unknown")) {
                    //System.out.println("*** " + s);
                    s = transformUnknownTaintedMapItem(s, analyzed_tainted_points);
                    //System.out.println("=== " + s);
                }
                Log.logData(using_method_structs, Utils.generatePartingLine("-"));
                Log.logData(using_method_structs, "+ Data structure: " + s);
                if (flag_suspicious == 1) {
                    Log.logData(suspicious_methods, Utils.generatePartingLine("-"));
                    Log.logData(suspicious_methods, "+ Data structure: " + s);
                    if (flag_suspicious_deduplicate == 0) {
                        Log.logData(suspicious_methods_final, Utils.generatePartingLine("-"));
                        Log.logData(suspicious_methods_final, "+ Data structure: " + s);
                    }
                }
            }
        }
        System.out.println("Suspicious method number: " + suspicious_method_num);
        System.out.println("Suspicious method number (remove deduplicate): " + suspicious_method_num_final);
    }


    public static void dataFlowAnalysisForBlocks(List<Block> blocks, List<Integer> path, int path_sensitive, Tainted entry, List<Value> entry_value_copies,
                                                 Map<Value, Value> newValueToCopy, Map<Value, String> numericValueToConcreteAssignment,Set<Value> tainted_entry_attributes,
                                                 Map<Value, String> taintedMapValueToTaintedItem, List<String> recorded_tainted_points, Map<Value, String> valueToField) {
        String entry_element = entry.getOuterElement();
        Unit start_unit = entry.getStartUnit();
        List<Tainted> entry_parents = entry.getParents();
        Set<AssignStmt> entry_assigns = entry.getEntryAssigns();

        // Copy the map.
        // Be specific to this path.
        Map<Value, Value> newValueToCopy_path = Utils.deepCopy(newValueToCopy);
        Map<Value, String> numericValueToConcreteAssignment_path = Utils.deepCopy(numericValueToConcreteAssignment);
        Map<Value, String> taintedMapValueToTaintedItem_path = Utils.deepCopy(taintedMapValueToTaintedItem);
        Map<Value, String> valueToField_path = Utils.deepCopy(valueToField);
        List<Value> entry_values_path = Utils.deepCopy(entry_value_copies);
        Set<Value> tainted_entry_attributes_path = Utils.deepCopy(tainted_entry_attributes);

        int flag_start = entry.getStartUnit() == null? 1:0;
        int flag_entry_assign = entry_assigns == null? 1:0;
        Value case_value = null; // The bridge value between two LookupSwithStmts.
        Value return_value = null; // A path has 0 or 1 return value.

        List<Value> tainted_values = new ArrayList<>();
        List<Unit> tainted_units = new ArrayList<>();

        for (int i = 0; i< path.size(); i++) {
            int block_id = path.get(i);
            Block block = blocks.get(block_id);
            for (Unit unit : block) {
                // If the entry has entry assignments,
                // the analysis should start with the first entry assignment.
                if(flag_entry_assign == 0){
                    if(unit instanceof AssignStmt){
                        if(entry_assigns.contains(((AssignStmt) unit))){
                            flag_entry_assign = 1;
                        }
                    }
                }
                if(flag_entry_assign == 0){
                    continue;
                }
                // If the entry sets a start unit,
                // the analysis should start with the start unit.
                if (flag_start == 0 && start_unit.equals(unit)) {
                    flag_start = 1;
                }
                if(flag_start == 0){
                    continue;
                }

                InvokeExpr ie = null;
                Value base = null;
                SootMethod callee = null;
                String callee_name = "NULL";

                int need_analysis = 0;
                int assignStmt = 0;
                int flag_attribute = 0; // Flag that whether the tainted value is the attribute of previously tainted value.
                int flag_attribute_entry = 0; // Flag that whether the tainted value is the attribute of the entry value.
                List<Value> involved_entry_values = new ArrayList<>(); // The entry values that this unit contains.
                List<Value> involved_pre_tainted_values = new ArrayList<>(); // The tainted values that this unit contains.

                if(unit instanceof TableSwitchStmt){
                    Utils.printPartingLine("!");
                    System.out.println("TableSwitchStmt: " + unit);
                    Utils.printPartingLine("!");
                    exit(0);
                }

                // Get return value.
                if(unit instanceof ReturnStmt){
                    ReturnStmt rs = (ReturnStmt) unit;
                    return_value = rs.getOp();
                    continue;
                }

                // Filter wrong paths.
                if(path_sensitive == 1) {
                    if (unit instanceof LookupSwitchStmt) {
                        LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                        if (case_value == null) { // Get the bridge case value between two LookupSwitchStmts.
                            case_value = getCaseValue(lss);
                        } else if (lss.getKey().equals(case_value)) {
                            boolean wrong_path = isWrongPathForSwitchStmt(analysis_data, blocks, path, i, lss, case_value, numericValueToConcreteAssignment_path);
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
                    } else if (unit instanceof IfStmt) {
                        IfStmt is = (IfStmt) unit;
                        boolean wrong_path = isWrongPathForIfStmt(blocks, path, i, is, numericValueToConcreteAssignment_path);
                        if (wrong_path) {
                            Utils.generatePartingLine("!");
                            Log.logData(analysis_data, "Wrong path, stop analyzing!");
                            Utils.generatePartingLine("!");
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
                    involved_entry_values = Utils.hasRightValuesOfAssignStmt(as, entry_values_path);
                    involved_pre_tainted_values = Utils.hasRightValuesOfAssignStmt(as, tainted_values);
                    if(!involved_entry_values.isEmpty() || !involved_pre_tainted_values.isEmpty()){
                        need_analysis = 1;
                    }
                    // This entry / tainted value has been re-defined.
                    if (need_analysis == 0) {
                        Unit pre_tainted_unit = tainted_units.isEmpty()? null : tainted_units.get(tainted_units.size() - 1);
                        Value redefined_value = hasRedefinedValue(as, ie, entry_values_path, pre_tainted_unit, entry_assigns, valueToField_path);
                        if (redefined_value != null) {
                            entry_values_path.remove(redefined_value);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(analysis_data, "+ Unit: " + as);
                            Log.logData(analysis_data, "--- The entry value [ " + as.getLeftOp() + " ] is re-defined, remove it.");
                            Log.logData(analysis_data, "--- Updated the entry value: " + entry_values_path);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                        } else {
                            redefined_value = hasRedefinedValue(as, ie, tainted_values, pre_tainted_unit, entry_assigns, valueToField_path);
                            if (redefined_value!=null) {
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                Log.logData(analysis_data, "+ Unit: " + as);
                                Log.logData(analysis_data, "--- The tainted value [ " + as.getLeftOp() + " ] is re-defined.");
                                // Store data structure when the tainted value is redefined.
                                Log.logData(analysis_data, "Store data structure -- Value re-definition.");
                                storeDataStructure(redefined_value, entry, taintedMapValueToTaintedItem_path, tainted_entry_attributes_path,
                                        valueToField_path, return_value, 0);
                                // Update the tainted value.
                                removePreviouslyTaintedValue(redefined_value, tainted_values, newValueToCopy_path);
                                Log.logData(analysis_data, "--- Update the tainted value: " + tainted_values);
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            }
                        }
                        // The entry value may be removed due to value re-defining.
                        // So we need add the entry value to the entry value list again.
                        if(entry_assigns!=null && entry_assigns.contains(as)){
                            if(!entry_values_path.contains(as.getLeftOp())){
                                entry_values_path.add(as.getLeftOp());
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                Log.logData(analysis_data, "+ Entry assignment: " + as);
                                Log.logData(analysis_data, "--- Updated the entry value: " + entry_values_path);
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            }
                        }
                    }
                    // Store useful information.
                    storeUsefulInfo(as, entry_values_path, newValueToCopy_path, numericValueToConcreteAssignment_path,
                            valueToField_path, taintedMapValueToTaintedItem_path, tainted_entry_attributes_path);
                } else if (unit instanceof InvokeStmt) {
                    ie = ((InvokeStmt) unit).getInvokeExpr();
                    base = Utils.getBaseOfInvokeExpr(ie);
                    callee_name = ie.getMethod().getName();
                    involved_entry_values = Utils.hasParametersOfInvokeExpr(ie, entry_values_path);
                    involved_pre_tainted_values = Utils.hasParametersOfInvokeExpr(ie, tainted_values);
                    if(!involved_entry_values.isEmpty() || !involved_pre_tainted_values.isEmpty()) {
                        need_analysis = 1;
                    } else if(callee_name.equals("toArray")){
                        if(entry_values_path.contains(base)){
                            involved_entry_values.add(base);
                            need_analysis = 1;
                        } else if (tainted_values.contains(base)){
                            involved_pre_tainted_values.add(base);
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
                if (!involved_entry_values.isEmpty()) {
                    Log.logData(analysis_data, "--- Tainted by the entry value: " + involved_entry_values);
                }
                if(!involved_pre_tainted_values.isEmpty()){
                    Log.logData(analysis_data, "--- Tainted by the tainted value: " + involved_pre_tainted_values);
                }
                // Focus on the entry / tainted value and its attributes.
                // If the tainted / entry value is passed in the callee, this callee is tainted.
                Set<Integer> tainted_param_indices = new HashSet<>();
                if (!involved_entry_values.isEmpty()) {
                    for (Value v : involved_entry_values) {
                        Integer param_index = Utils.isParameterOfInvokeExpr(ie, v);
                        if (param_index != -1) {
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if (!involved_pre_tainted_values.isEmpty()) {
                    for (Value v : involved_pre_tainted_values) {
                        Integer param_index = Utils.isParameterOfInvokeExpr(ie, v);
                        if (param_index != -1) {
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if (!tainted_param_indices.isEmpty()) {
                    Log.logData(analysis_data, "--- Tainted callee.");
                    int construct_method = 0;
                    if (canFilterForTaintedParameter(base, callee, callee_name)) {
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    // For the tainted method related to data removing, we record the involved data struct.
                    if(callee_name.startsWith("remove") || callee_name.startsWith("delete")){
                        Value involved_removed_struct = getInvolvedRemovedStruct(assignStmt, base, callee_name, unit);
                        if(involved_removed_struct!=null) {
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(analysis_data, "Store data structure -- Data removing.");
                            storeDataStructure(involved_removed_struct, entry, taintedMapValueToTaintedItem_path, tainted_entry_attributes_path,
                                    valueToField_path, return_value, 1);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            continue;
                        }
                    }
                    if ("add_addAll_put_putAll_append".contains(callee_name)) { // xxx.add(tainted_value)
                        if (base != null) {
                            // Update the tainted map value.
                            if(Utils.isMapValue(base)){
                                String tainted_map_item = confirmTaintedItemOfTaintedMap(callee_name, ie, tainted_param_indices,
                                        tainted_units, taintedMapValueToTaintedItem_path);
                                storeTaintedMapValueAndCorrespondingTaintedItem(base, tainted_map_item, taintedMapValueToTaintedItem_path,
                                        newValueToCopy_path);
                            }
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, entry_values_path, tainted_values, newValueToCopy_path);
                            tainted_units.add(unit);
                            continue;
                        } else if(assignStmt == 1){
                            // Update the tainted map value.
                            AssignStmt as = (AssignStmt) unit;
                            if(Utils.isMapValue(as.getLeftOp())){
                                String tainted_map_item = confirmTaintedItemOfTaintedMap(callee_name, ie, tainted_param_indices,
                                        tainted_units, taintedMapValueToTaintedItem_path);
                                storeTaintedMapValueAndCorrespondingTaintedItem(as.getLeftOp(), tainted_map_item, taintedMapValueToTaintedItem_path,
                                        newValueToCopy_path);
                            }
                        }
                    }
                    if (callee_name.equals("arraycopy")) {
                        // Update the tainted value.
                        Value newly_tainted_value = ie.getArg(2);
                        updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, entry_values_path, tainted_values, newValueToCopy_path);
                        tainted_units.add(unit);
                        continue;
                    }
                    if (callee.isConstructor()) { // Constructor should be record, because the tainted value will be put into a field.
                        if (base != null) {
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, entry_values_path, tainted_values, newValueToCopy_path);
                            tainted_units.add(unit);
                            //continue;
                            construct_method = 1;
                        }
                    }
                    // Record the newly tainted method.
                    Map<Integer, String> involved_tainted_mapItems = new HashMap<>();
                    Set<Integer> involved_tainted_attributes = new HashSet<>();
                    getInvolvedTaintedObjectsFromTaintedParams(ie, tainted_param_indices, taintedMapValueToTaintedItem_path, tainted_entry_attributes_path,
                            involved_tainted_mapItems, involved_tainted_attributes);
                    if (needRecordMethod(assignStmt, callee, base, unit)) {
                        String tainted_point_sig = tainted_param_indices + involved_tainted_mapItems.toString();
                        if((ie instanceof InterfaceInvokeExpr) && base!=null) { // For an Interface invoking, different bases may correspond to different implemented methods.
                            tainted_point_sig += unit;
                        } else {
                            tainted_point_sig += callee.getSignature();
                        }
                        if (!recorded_tainted_points.contains(tainted_point_sig)) { // This tainted point has not been stored.
                            Log.logData(analysis_data, "--- Record the tainted method: " + callee_name);
                            recorded_tainted_points.add(tainted_point_sig);
                            Tainted child = new Tainted(callee, tainted_param_indices, unit, involved_tainted_mapItems);
                            child.setTaintedAttributes(involved_tainted_attributes);
                            entry.storeTaintedChild(child);
                            List<Tainted> parents = Utils.deepCopy(entry_parents);
                            parents.add(entry);
                            Tainted newly_tainted_point = new Tainted(callee, tainted_param_indices, entry_element, parents, unit, involved_tainted_mapItems);
                            newly_tainted_point.setTaintedAttributes(involved_tainted_attributes);
                            tainted_points.offer(newly_tainted_point);
                        } else {
                            Log.logData(analysis_data, "--- This tainted method has been recoded.");
                        }
                    }
                    // For the constructor, we have update the tainted value list before.
                    if(construct_method==1){
                        continue;
                    }
                    // For the tainted method related to data removing, we don't update the tainted value list.
                    if(callee_name.startsWith("remove") || callee_name.startsWith("delete")
                            || callee_name.startsWith("unregister")){
                        Log.logData(analysis_data, "--- No need to update the tainted value.");
                        continue;
                    }
                    // Judge whether the tainted value is a tainted attribute of the entry value.
                    int attribute_type = isTaintedAttribute(callee_name, base, involved_tainted_attributes);
                    if(attribute_type == 1){
                        flag_attribute = 1;
                    } else if(attribute_type == 2){
                        flag_attribute = 1;
                        flag_attribute_entry = 1;
                    }
                } else {
                    if (base != null) {
                        if (involved_entry_values.contains(base) || involved_pre_tainted_values.contains(base)) {
                            Log.logData(analysis_data, "--- Tainted base.");
                            if(canFilterForTaintedBase(base, callee_name)){
                                Log.logData(analysis_data, "--- Pass.");
                                continue;
                            }
                            if(callee_name.equals("toArray") && (!ie.getArgs().isEmpty())){
                                // Update the tainted value.
                                Value newly_tainted_value = ie.getArg(0);
                                updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, entry_values_path, tainted_values, newValueToCopy_path);
                                tainted_units.add(unit);
                                continue;
                            }
                            int attribute_type = isTaintedAttribute(base, callee_name, tainted_entry_attributes_path);
                            if(attribute_type == 1){
                                flag_attribute = 1;
                            }else if(attribute_type == 2){
                                flag_attribute = 1;
                                flag_attribute_entry = 1;
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
                    // Judge whether the newly tainted value is a tainted attribute.
                    if (ie == null) {
                        String right_op = as.getRightOp().toString();
                        if (right_op.startsWith("lengthof")) {
                            Log.logData(analysis_data, "--- Pass.");
                            continue;
                        }
                        int attribute_type = isTaintedAttribute(as, tainted_entry_attributes_path);
                        if(attribute_type == 1){
                            flag_attribute = 1;
                        } else if(attribute_type == 2){
                            flag_attribute = 1;
                            flag_attribute_entry = 1;
                        }
                    }
                    // Update the Map value information.
                    updateTaintedMapValueInfo(as, ie, tainted_units, taintedMapValueToTaintedItem_path, newValueToCopy_path);
                    // Update the tainted value.
                    // If the newly tainted value is the attribute of the previously tainted value,
                    // or the previously tainted involves a judgement, record it.
                    Value newly_tainted_value = as.getLeftOp();
                    if((flag_attribute == 1 && !"iterator".contains(callee_name) && !callee_name.startsWith("next")
                            && !as.getRightOp().toString().startsWith("("))
                            || newly_tainted_value.getType().toString().equals("boolean")){
                        addNewlyTaintedValue(newly_tainted_value, tainted_values, newValueToCopy_path);
                        Log.logData(analysis_data, "--- Update the tainted value: " + tainted_values);
                    } else {
                        updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, entry_values_path, tainted_values, newValueToCopy_path);
                    }
                    // Record the attribute to distinguish the tainted values more finely.
                    updateTaintedAttributesFromEntry(flag_attribute_entry, newly_tainted_value, tainted_entry_attributes_path);
                }
                tainted_units.add(unit);
            }
        }

        // Store some information.
        Log.logData(analysis_data, Utils.generatePartingLine("="));
        Log.logData(analysis_data, "Store data structure -- Analysis complete.");
        if(entry_values_path.contains(return_value)){
            tainted_values.add(return_value);
        }
        if(tainted_values.isEmpty()){
            tainted_values.add(null);
        }
        for(Value v : tainted_values) {
            storeDataStructure(v, entry, taintedMapValueToTaintedItem_path, tainted_entry_attributes_path, valueToField_path, return_value, 0);
        }
    }

    public static void dataFlowAnalysisForMethod(Tainted entry){
        SootMethod entry_method = entry.getMethod();
        Body body = null;
        if (entry_method.isConcrete()) {
            body = entry_method.retrieveActiveBody();
        } else {
            Utils.printPartingLine("!");
            System.out.println("This method does not have a body: " + entry_method);
            if(entry_method.isNative()) {
                System.out.println("Native method.");
            } else if(entry_method.isPhantom()) {
                System.out.println("Phantom method.");
            }
            Utils.printPartingLine("!");
            exit(0);
        }

        // Get the entry values.
        // Initialize the Map value information, attributes information.
        List<Value> entry_values = entry.getTaintedValues();
        Map<Integer, String> entry_mapItem = entry.getTaintedMapItem();
        Map<Value, String> taintedMapValueToTaintedItem = new HashMap<>();
        Set<Integer> entry_attributes = entry.getTaintedAttributes();
        Set<Value> tainted_entry_attributes = new HashSet<>();
        if(entry_values == null) {
            Set<Integer> entry_param_indices = entry.getTaintedParamIndices();
            entry_values = new ArrayList<>();
            for (int param_index : entry_param_indices) {
                Value parameter = Utils.getParameterOfMethod(body, param_index);
                if (parameter != null) {
                    entry_values.add(parameter);
                    if(entry_mapItem!=null && entry_mapItem.containsKey(param_index)){
                        taintedMapValueToTaintedItem.put(parameter, entry_mapItem.get(param_index));
                    }
                    if(entry_attributes!=null && entry_attributes.contains(param_index)){
                        tainted_entry_attributes.add(parameter);
                    }
                } else {
                    Utils.printPartingLine("!");
                    System.out.println("Null parameter.");
                    System.out.println("method: " + entry_method.getSignature());
                    System.out.println("parameter index: " + param_index);
                    Utils.printPartingLine("!");
                    exit(0);
                }
            }
        } else {
            for(Value entry_value : entry_values){
                if(Utils.isMapValue(entry_value)){
                    taintedMapValueToTaintedItem.put(entry_value, "_value");
                }
                tainted_entry_attributes.add(entry_value);
            }
        }

        Log.logData(analysis_data, "+ Entry value: " + entry_values);
        Log.logData(analysis_data, "+ Entry map item: " + taintedMapValueToTaintedItem);
        Log.logData(analysis_data, "+ Entry attributes: " + tainted_entry_attributes);
        Utils.printPartingLine("=");
        System.out.println("+ Method: " + entry_method.getName());
        System.out.println("+ Entry value: " + entry_values);
        System.out.println("+ Entry map item: " + taintedMapValueToTaintedItem);
        System.out.println("+ Entry attributes: " + tainted_entry_attributes);

        // Construct the block graph.
        CompleteBlockGraph cbg = new CompleteBlockGraph(body);

        Log.logBody(body);
        Log.logCBG(cbg);

        Map<Value, String> numericValueToConcreteAssignment = new HashMap<Value, String>(); // The concrete value of all numeric Values (iX, bX, zX).
        Map<Value, Value> newValueToCopy = new HashMap<Value, Value>(); // The newly constructed object and its copy.
        Map<Value, String> valueToField = new HashMap<>(); // The value related to a field.

        List<Value> entry_value_copies = Utils.deepCopy(entry_values);

        // To avoid path explosion caused by massive blocks, we start our analysis with the block we are interested in.
        // Because we ignore some blocks directly, we need save some useful information from them.
        int path_sensitive = 1;
        Block start_block;
        System.out.println("Find start block...");
        if(path_insensitive_methods.contains(entry_method.getName())) { // This method is unsuitable for the path-sensitive 
            start_block = findStartBlock(cbg, entry, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment,
                    valueToField, taintedMapValueToTaintedItem, tainted_entry_attributes);
            path_sensitive = 0;
        } else {
            List<Block> interested_blocks = findAllInterestedBlocks(cbg, entry, entry_value_copies, entry.getEntryAssigns());
            start_block = findStartBlock(interested_blocks, cbg, entry, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment,
                    valueToField, taintedMapValueToTaintedItem, tainted_entry_attributes);
        }
        if (start_block == null) {
            entry.storeDataStructure(null);
            Log.logData(analysis_data, "This method does not need to be analyzed.");
            Utils.printPartingLine("!");
            System.out.println("Cannot find the start block.");
            Utils.printPartingLine("!");
            return;
        }

        System.out.println("+ Start block id: " + start_block.getIndexInMethod());
        System.out.println("+ Parameters: " + entry.getParameters());
        System.out.println("+ Numeric: " + numericValueToConcreteAssignment);
        // Log data.
        Log.logData(analysis_data, "+ Start block id: " + start_block.getIndexInMethod());

        System.out.println("Generate path...");
        if(path_sensitive == 0) { // This method is unsuitable for the path-sensitive 
            List<Integer> path = new ArrayList<>();
            for (int i = start_block.getIndexInMethod(); i < cbg.getBlocks().size(); i++) {
                path.add(i);
            }
            Graph.paths.add(path);
        }else {
            Graph.generatePathsFromBlock(start_block);
            boolean duplicated = Utils.hasDuplicatedItems(Graph.paths);
            if (duplicated) {
                Utils.printPartingLine("!");
                System.out.println("Exist duplicated paths.");
                Utils.printPartingLine("!");
                exit(0);
            } else {
                System.out.println("No duplicated paths.");
            }
        }

        int total_num = Graph.paths.size();
        System.out.println("+ Total path num: " + total_num);

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
            dataFlowAnalysisForBlocks(cbg.getBlocks(), path, path_sensitive, entry, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment,
                    tainted_entry_attributes, taintedMapValueToTaintedItem, recorded_tainted_points, valueToField);
            path_num+=1;
            if(path_num == total_num || path_num % 1000 == 0) {
                System.out.println("Analyzed path num: " + path_num);
            }

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
                    String likely_field = getField(as);
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
                                    SootMethod implemented_method = getImplementedMethodOfAbstractMethod(null, ifi, entry_point);
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
