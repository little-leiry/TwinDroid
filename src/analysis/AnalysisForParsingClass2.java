package analysis;

import graph.Graph;
import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.scalar.Pair;

import java.util.*;

import static java.lang.System.exit;

public class AnalysisForParsingClass2 extends Analysis {
    // The class for parsing an apk.
    public static final String parsing_class = "android.content.pm.parsing.ParsingPackageUtils";
    // The class for store the parsed package's settings.
    public static final String parsedPackage_settings_class = "android.content.pm.parsing.ParsingPackageImpl";

    // The tainted_methods needed to be analysed.
    // Each object consists of <tainted method, tainted value, associated element>
    // Use queue to do BFS.
    public static Queue<BU> tainted_points = new LinkedList<BU>();

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

    // Our analysis is path-sensitive. We analyze each path of a method's block graph.
    // But some methods is unsuitable for path-sensitive analysis.
    // In general, these methods contains many If statements,
    // and will generate lots of redundant paths.
    public static List<String> path_insensitive_methods = new ArrayList<>();

    public static final String element_data = "logs/parsing2/element_data.txt";
    public static final String method_data = "logs/parsing2/method_data.txt";
    public static String analysis_data = "logs/parsing2/analysis_data.txt";
    public static String suspicious_structures = "logs/parsing2/suspicious_structures.txt";

    public static String pkg_structures = "logs/parsing2/pkg_structures.txt";

    public static boolean isInterestedUnit(Unit unit, List<Value> entry_value_copies, Map<Value, String> stringValueToLikelyElement){
        if(unit instanceof AssignStmt){
            AssignStmt as =(AssignStmt) unit;
            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- Related to elements.
            if (getRelatedElement(ie, stringValueToLikelyElement) != null) {
                return true;
            }
            // Interested unit -- the entry value appears in the right of the Assignment unit.
            if(!Utils.hasRightValuesOfAssignStmt(as, entry_value_copies).isEmpty()) {
                // Filter some uninterested types.
                if(Utils.hasCopyOfValues(as, entry_value_copies)){
                    return false;
                }
                if (entry_value_copies.contains(base)) {
                    String method_name = ie.getMethod().getName();
                    if(canFilterForTaintedBase(base, method_name)){
                        return false;
                    }
                }
                if (!Utils.hasParametersOfInvokeExpr(ie, entry_value_copies).isEmpty()) {
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
            // Interested unit -- pass in the entry value as a parameter.
            if (!Utils.hasParametersOfInvokeExpr(ie, entry_value_copies).isEmpty()) {
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

    public static boolean isSpecialMethod(String method_name){
        String[]  sms = {"parseUsesPermission", "parseUsesSdk", "parseKeySets", "parseQueries", "parseUsesStaticLibrary"};
        List<String> special_methods = new ArrayList<>(Arrays.asList(sms));
        if(special_methods.contains(method_name)){
            return true;
        }
        return false;
    }

    public static boolean isSuspiciousDataStructure(String ds){
        if(ds!=null && ds.contains("<") && ds.contains(parsedPackage_settings_class)) {
            String type = ds.split(" ")[1];
            if ((type.endsWith("Map") || type.endsWith("SparseArray"))){ // For the type of Map
                if(ds.endsWith("value") && !ds.contains("key(name)")){
                    return true;
                }
            }
            if(type.endsWith("List") || type.endsWith("[]") || type.endsWith("Queue") || type.endsWith("Stack")) {
                return true;
            }
        }
        return false;
    }

    public static boolean isTaintedAttribute(String method_name){
        if(method_name.startsWith("get")){
            //System.out.println("=== " + ie);
            return true;
        }
        return false;
    }

    public static boolean isTaintedAttribute(Value base, String method_name){
        if(base != null){
            // $r6 = virtualinvoke r4.<android.content.pm.parsing.component.ParsedProvider: java.lang.String getAuthority()>()
            // $r7 = virtualinvoke $r6.<java.lang.String: java.lang.String[] split(java.lang.String)>(";")
            if(method_name.startsWith("get") || "split_values_keySet_entrySet".contains(method_name)){
                return true;
            }
        }
        return false;
    }

    public static boolean isTaintedAttribute(AssignStmt as){
        List<ValueBox> vbs = as.getUseBoxes();
        String right_op = as.getRightOp().toString();
        Value likely_attribute = null;
        if (vbs.size() == 1){
            if(Utils.isCopyStmt(as)) {
                likely_attribute = as.getRightOp();
            }
        }else if(vbs.size() == 2) {
            // $r6 = $r5.<android.content.pm.parsing.component.ParsedAttribution: java.lang.String tag>
            if(right_op.contains(".<")){
                likely_attribute = vbs.get(1).getValue();
            }
        } else if (vbs.size() == 3){
            // $r6 = $r7[i2]
            if(right_op.contains("[")){
                likely_attribute = vbs.get(1).getValue();
            }
        }
        if(likely_attribute!=null) {
            return true;
        }
        return false;
    }



    public static boolean canFilterForTaintedBase(Value base, String method_name){
        String base_type = base.getType().toString();
        String declaring_class = ((RefType) base.getType()).getSootClass().getName();

        if (base_type.endsWith("parsing.result.ParseResult")) {
            if (!method_name.equals("getResult")) { // result.getResult()
                return true;
            }
        }
        if(base_type.equals("android.content.res.XmlResourceParser")){
            if(!method_name.equals("getName")){
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
        if (method_name.startsWith("remove")) {
            return true;
        }
        return false;
    }

    public static boolean needRecordMethod(int assignStmt, int flag_parser, String callee_name){
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

    public static String getRelatedElement(InvokeExpr ie, Map<Value, String> stringValueToLikelyElement){
        if(ie == null) return null;

        String method_name = ie.getMethod().getName();
        Value base = Utils.getBaseOfInvokeExpr(ie);

        if (method_name.equals("equals")) {
            if (ie.getArg(0) instanceof StringConstant) { // parser.getName().equals(element)
                String s = ie.getArg(0).toString();
                if (!skip_names.contains(s) && ! s.startsWith("\"android.permission") && !s.startsWith("\"/")) {
                    return s;
                }
            } else if (base != null && stringValueToLikelyElement!=null) { // element.equals(parser.getName())
                if (stringValueToLikelyElement.containsKey(base)) {
                    return stringValueToLikelyElement.get(base);
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
    public static void storeStringValueAndCorrespondingLikelyElement(AssignStmt as, Map<Value, String> stringValueToLikelyElement){
        if(as == null) return;

        if (as.getUseBoxes().size()==1) {
            Value left_value = as.getLeftOp();
            Value right_op = as.getRightOp();
            if(right_op instanceof StringConstant) { // $r4 = "manifest"
                String likely_element = right_op.toString();
                if (likely_element.startsWith("\"/")) return;
                if (likely_element.startsWith("\"android.permission")) return;
                if (skip_names.contains(likely_element)) return;
                stringValueToLikelyElement.put(left_value, likely_element);
                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                Log.logData(analysis_data, "Likely element: " + as);
                Log.logData(analysis_data, Utils.generatePartingLine("+"));
            } else if(stringValueToLikelyElement.containsKey(right_op)){ // $r3 = $r4
                String likely_element = stringValueToLikelyElement.get(right_op);
                stringValueToLikelyElement.put(left_value, likely_element);
                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                Log.logData(analysis_data, "Likely element: " + as + " = " +  likely_element);
                Log.logData(analysis_data, Utils.generatePartingLine("+"));
            } else if(stringValueToLikelyElement.containsKey(left_value)){ // This String value is re-defined.
                stringValueToLikelyElement.remove(left_value);
            }
        } else if(stringValueToLikelyElement.containsKey(as.getLeftOp())){ // This String value is re-defined.
            stringValueToLikelyElement.remove(as.getLeftOp());
        }
    }

    public static void storeUsefulInfo(AssignStmt as, List<Value> entry_value_copies, Map<Value, Value> newValeToCopy, Map<Value, String> numericValueToConcreteAssignment,
                                       Map<Value, String> stringValueToLikelyElement, Map<Value, String> valueToField,
                                       Map<Value, String> mapValueToTaintedItem){
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
        }
        storeNewValueAndCorrespondingCopy(as, newValeToCopy);
        storeStringValueAndCorrespondingLikelyElement(as, stringValueToLikelyElement);
        storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment);
        storeValueAndCorrespondingField(as, valueToField);
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
                    if(Utils.hasParametersOfInvokeExpr(ie, entry_value_copies) != null){
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

    public static String transformUnknownTaintedMapItem(String ds, List<BU> analyzed_tainted_points){
        String method_sig = ds.split("unknown\\(")[1].split(">")[0] + ">";
        int flag_known = 0;
        for(BU point : analyzed_tainted_points){
            if(point.getMethod().getSignature().equals(method_sig)){
                List<Pair<String, String>> e_ds = point.getInnerElementAndStructures();
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
                String tainted_item = bridge.split("_map")[1];
                if(tainted_item.contains("unknown")){
                    method_sig = tainted_item.split("unknown\\(")[1].split(">")[0] + ">";
                    continue;
                }
                ds = ds.split("_unknown")[0] + tainted_item;
                flag_known = 1;
            }
            if(flag_known == 1){
                break;
            }
        }
        return ds;
    }

    public static void updateTaintedValues(Value newly_tainted_value, List<Value> involved_pre_tainted_values, List<Value> tainted_values, Map<Value, Value> newValueToCopy, String callee_name){
        // Update the tainted value.
        if(!involved_pre_tainted_values.isEmpty()) {
            // Remove the previously tainted value.
            for(Value v : involved_pre_tainted_values) {
                if (v.getType().toString().endsWith("parsing.result.ParseResult") && !callee_name.equals("getResult")) {
                    Log.logData(analysis_data, "--- Cannot update the tainted value: " + v);
                    return;
                }
                removePreviouslyTaintedValue(v, tainted_values, newValueToCopy);
            }
        }
        // Add the newly tainted value.
        addNewlyTaintedValue(newly_tainted_value, tainted_values, newValueToCopy);
        Log.logData(analysis_data, "--- Update the tainted value: " + tainted_values);
    }

    // Find the blocks that contains the interested units.
    public static List<Block> findAllInterestedBlocks(CompleteBlockGraph cbg, BU entry, List<Value> entry_value_copies, Set<AssignStmt> entry_assigns,
                                                      Map<Value, String> stringValueToLikelyElement){
        List<Block> interested_blocks = new ArrayList<>();
        String ids = " ";
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
                    if(isInterestedUnit(unit, entry_value_copies, stringValueToLikelyElement)){
                        flag_interested = 1;
                    }else if(unit instanceof SwitchStmt){
                        // For switch-case statement, we need to analyze each case.
                        SwitchStmt ss = (SwitchStmt) unit;
                        for (int i = 0; i < ss.getTargets().size(); i++) {
                            Unit u = ss.getTarget(i);
                            if(isInterestedUnit(u, entry_value_copies, stringValueToLikelyElement)) {
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
                    ids += block.getIndexInMethod() + "_";
                    break;
                }
            }
        }
        System.out.println("Interested blocks: " + ids);
        return interested_blocks;
    }
    // For path-sensitive analysis.
    // Find the LCA block of all interested blocks (including the block in the interested blocks) .
    public static Block findStartBlock(List<Block> interested_blocks, CompleteBlockGraph cbg, BU entry, List<Value> entry_value_copies,
                                       Map<Value, Value> newValueToCopy, Map<Value, String> numericValueToConcreteAssignment,
                                       Map<Value, String> stringValueToLikelyElement, Map<Value, String> valueToField,
                                       Map<Value, String> mapValueToTaintedItem){
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
                            stringValueToLikelyElement, valueToField, mapValueToTaintedItem);
                }
            }
        }
        return null;
    }
    // For path-insensitive analysis.
    public static Block findStartBlock(CompleteBlockGraph cbg, BU bu, List<Value> source_variables, Map<Value, Value> newValueToCopy,
                                       Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> stringValueToLikelyElement,
                                       Map<Value, String> valueToField, Map<Value, String> mapValueToTaintedItem){
        if(cbg==null || bu == null || source_variables == null) return null;

        Block start_block = null;
        int entry_assign = bu.getEntryAssigns() == null? 0:1;

        for(Block block : cbg.getBlocks()){
            for(Unit unit : block){
                if(entry_assign == 1){
                    if(unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        if (bu.getEntryAssigns().contains(as)) {
                            System.out.println("Interested unit: " + unit);
                            bu.setStartUnit(as);
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
                                if (bu.getEntryAssigns().contains(as)) {
                                    System.out.println("Interested unit: " + unit);
                                    bu.setStartUnit(as);
                                    start_block = block;
                                    break;
                                }
                            }
                        }
                        if(start_block!=null) break;
                    }
                } else {
                    if (isInterestedUnit(unit, source_variables, stringValueToLikelyElement)) {
                        System.out.println("Interested unit: " + unit);
                        bu.setStartUnit(unit);
                        start_block = block;
                        break;
                    }
                    if (unit instanceof SwitchStmt) {
                        // For switch-case statement, we need to analyze each case.
                        SwitchStmt ss = (SwitchStmt) unit;
                        for (int i = 0; i < ss.getTargets().size(); i++) {
                            Unit u = ss.getTarget(i);
                            if (isInterestedUnit(u, source_variables, stringValueToLikelyElement)) {
                                System.out.println("Interested unit: " + unit);
                                bu.setStartUnit(unit);
                                start_block = block;
                                break;
                            }
                        }
                        if (start_block != null) break;
                    }
                }
                if(unit instanceof AssignStmt) {
                    // Store some information before we skip the unit.
                    AssignStmt as = (AssignStmt) unit;
                    storeUsefulInfo(as, source_variables, newValueToCopy, numericValueToConcreteAssignment,
                            stringValueToLikelyElement, valueToField, mapValueToTaintedItem);
                }
            }
            if(start_block != null) break;
        }
        return start_block;
    }

    // For an element in the app's manifest,
    // the system will invoke the corresponding parsing method to parse it,
    // and get its parsing result.
    // For example: for the element <permission>, its parse method is parsePermission,
    // the parsing result is ParsedPermission.
    // So, during analyzing, we treat the tainted / entry value as a whole,
    // ignore the part (ie., the attribute) of it.
    // The attributes are wrapped in the parsing result.
    public static void dataFlowAnalysisForBlocks(List<Block> blocks, List<Integer> path, int path_sensitive, BU base_unit, List<Value> source_variables, Map<Value, Value> newValueToCopy,
                                                 Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> mapValueToTaintedItem,
                                                 List<String> recorded_tainted_points, Map<Value, String> stringValueToLikelyElement,
                                                 Map<Value, String> valueToField) {

        String base_element = base_unit.getOuterElement();
        Unit start_unit = base_unit.getStartUnit();
        List<BU> base_parents = base_unit.getParents();
        Set<AssignStmt> source_defs = base_unit.getEntryAssigns();

        // Copy the map.
        // Specific to this path.
        Map<Value, Value> newValueToCopy_path = Utils.deepCopy(newValueToCopy);
        Map<Value, String> numericValueToConcreteAssignment_path = Utils.deepCopy(numericValueToConcreteAssignment);
        Map<Value, String> mapValueToTaintedItem_path = Utils.deepCopy(mapValueToTaintedItem);
        Map<Value, String> stringValueToLikelyElement_path = Utils.deepCopy(stringValueToLikelyElement);
        Map<Value, String> valueToField_path = Utils.deepCopy(valueToField);
        List<Value> source_variables_path = Utils.deepCopy(source_variables);

        String element = null; // This element related to this path.
        String data_structure = null;
        Value return_value = null;

        List<Value> passing_variables = new ArrayList<>(); // The variables into which the data stored in the source variables flow.
        List<Unit> passing_unit = new ArrayList<>(); // The statements that trigger the variable propagation.

        int flag_start = base_unit.getStartUnit() == null? 1:0;
        int flag_source_def = source_defs==null? 1:0;

        for (int i = 0; i< path.size(); i++) {
            int block_id = path.get(i);
            Block block = blocks.get(block_id);
            for (Unit unit : block) {
                // If there are source variable's definition statements,
                // the analysis scope is under the first definition statements.
                if(flag_source_def == 0){
                    if(unit instanceof AssignStmt){
                        if(source_defs.contains(((AssignStmt) unit))){
                            flag_source_def = 1;
                        }
                    }
                }
                if(flag_source_def == 0){
                    continue;
                }

                // If the base unit sets a start statement,
                // the analysis scope should be under this start statement.
                if (flag_start == 0 && start_unit.equals(unit)) {
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
                int flag_attribute = 0;
                List<Value> involved_entry_values = new ArrayList<>(); // The entry values that this unit contains.
                List<Value> involved_pre_tainted_values = new ArrayList<>(); // The tainted values that this unit contains.

                // Get the return value.
                if(unit instanceof ReturnStmt){
                    return_value = ((ReturnStmt) unit).getOp();
                    continue;
                }

                // Filter wrong paths.
                if(path_sensitive == 1) {
                    if (unit instanceof LookupSwitchStmt) {
                        LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                        Value case_value = lss.getKey();
                        boolean wrong_path = isWrongPathForSwitchStmt(analysis_data, blocks, path, i, lss, case_value, numericValueToConcreteAssignment_path);
                        if (wrong_path) {
                            Utils.generatePartingLine("!");
                            Log.logData(analysis_data, "Wrong path, stop analyzing!");
                            Utils.generatePartingLine("!");
                            return;
                        }
                    }else if (unit instanceof IfStmt) {
                        IfStmt is = (IfStmt) unit;
                        boolean wrong_path = isWrongPathForIfStmt(blocks, path, i, is, numericValueToConcreteAssignment_path);
                        if (wrong_path) {
                            Utils.generatePartingLine("!");
                            Log.logData(analysis_data, "--- Wrong path, stop analyzing!");
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
                    involved_entry_values = Utils.hasRightValuesOfAssignStmt(as, source_variables_path);
                    involved_pre_tainted_values = Utils.hasRightValuesOfAssignStmt(as, passing_variables);
                    if(!involved_entry_values.isEmpty() || !involved_pre_tainted_values.isEmpty()){
                        need_analysis = 1;
                    }
                    // This entry / tainted value has been re-defined.
                    if (need_analysis == 0) {
                        Unit pre_tainted_unit = passing_unit.isEmpty()?  null : passing_unit.get(passing_unit.size() - 1);
                        Value redefined_value = hasRedefinedValue(as, ie, source_variables_path, pre_tainted_unit, source_defs, valueToField_path);
                        if (redefined_value != null) {
                            source_variables_path.remove(redefined_value);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(analysis_data, "+ Unit: " + as);
                            Log.logData(analysis_data, "--- The entry value [ " + as.getLeftOp() + " ] is re-defined, remove it.");
                            Log.logData(analysis_data, "--- Updated the entry value: " + source_variables_path);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                        } else {
                            redefined_value = hasRedefinedValue(as, ie, passing_variables, pre_tainted_unit, source_defs, valueToField_path);
                            if (redefined_value!=null) {
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                Log.logData(analysis_data, "+ Unit: " + as);
                                Log.logData(analysis_data, "--- The tainted value [ " + as.getLeftOp() + " ] is re-defined.");
                                data_structure = getDataStructure(redefined_value, mapValueToTaintedItem_path, valueToField_path,
                                        null, return_value, 0); // Store some information when the tainted value is redefined.
                                Log.logData(analysis_data, "Store the information -- value re-defined.");
                                base_unit.storeInnerElementAndStructure2(element, data_structure); // This element only related to the entry method.
                                String associated_element = getAssociatedElement(base_element, element); // This element related to the entry method and its parents.
                                storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
                                removePreviouslyTaintedValue(redefined_value, passing_variables, newValueToCopy_path);
                                Log.logData(analysis_data, "--- Update the tainted value: " + passing_variables);
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            }
                        }
                        // The entry value may be removed due to value re-defining.
                        // So we need add the entry value to the entry value list again.
                        if(source_defs!=null && source_defs.contains(as)){
                            if(!source_variables_path.contains(as.getLeftOp())){
                                source_variables_path.add(as.getLeftOp());
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                Log.logData(analysis_data, "+ Entry assignment: " + as);
                                Log.logData(analysis_data, "--- Updated the entry value: " + source_variables_path);
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            }
                        }
                    }
                    // Store useful information.
                    storeUsefulInfo(as, source_variables_path, newValueToCopy_path, numericValueToConcreteAssignment_path,
                            stringValueToLikelyElement_path, valueToField_path, mapValueToTaintedItem_path);
                } else if (unit instanceof InvokeStmt) {
                    ie = ((InvokeStmt) unit).getInvokeExpr();
                    base = Utils.getBaseOfInvokeExpr(ie);
                    callee_name = ie.getMethod().getName();
                    involved_entry_values = Utils.hasParametersOfInvokeExpr(ie, source_variables_path);
                    involved_pre_tainted_values = Utils.hasParametersOfInvokeExpr(ie, passing_variables);
                    if(!involved_entry_values.isEmpty() || !involved_pre_tainted_values.isEmpty()) {
                        need_analysis = 1;
                    } else if(callee_name.equals("toArray")){
                        if(source_variables_path.contains(base)){
                            involved_entry_values.add(base);
                            need_analysis = 1;
                        } else if (passing_variables.contains(base)){
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

                // Get the element's name.
                String s = getRelatedElement(ie, stringValueToLikelyElement_path);
                if (s != null){
                    // Store some information before update the element.
                    // Have solved one element case.
                    // Or have tainted some values that irrelevant to this element.
                    String old_element = element;
                    if(old_element != null || !passing_variables.isEmpty()) {
                        // Store some information before updating the element.
                        Log.logData(analysis_data, Utils.generatePartingLine("="));
                        Log.logData(analysis_data, "Store information -- element update.");
                        if(passing_variables.isEmpty()){
                            passing_variables.add(null);
                        }
                        for(Value v : passing_variables){
                            data_structure = getDataStructure(v, mapValueToTaintedItem_path, valueToField_path,
                                    null, return_value, 0);
                            base_unit.storeInnerElementAndStructure2(old_element, data_structure); // This element only related to the entry method.
                            String associated_element = getAssociatedElement(base_element, old_element); // This element related to the entry method and its parents.
                            storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
                        }
                        passing_variables.clear();
                        passing_unit.clear();
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
                    Log.logData(analysis_data, "--- Tainted by the entry value: " + involved_entry_values);
                }
                if(!involved_pre_tainted_values.isEmpty()){
                    Log.logData(analysis_data, "--- Tainted by the tainted value: " + involved_pre_tainted_values);
                }

                // If the tainted / entry value is passed in the callee, this callee is tainted.
                Set<Integer> tainted_param_indices = new HashSet<>();
                if(!involved_entry_values.isEmpty()){
                    for(Value v : involved_entry_values){
                        Integer param_index = Utils.isParameterOfInvokeExpr(ie, v);
                        if(param_index!=-1){
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if(!involved_pre_tainted_values.isEmpty()){
                    for(Value v : involved_pre_tainted_values){
                        Integer param_index = Utils.isParameterOfInvokeExpr(ie, v);
                        if(param_index!=-1){
                            tainted_param_indices.add(param_index);
                        }
                    }
                }
                if(!tainted_param_indices.isEmpty()){
                    Log.logData(analysis_data, "--- Tainted callee.");
                    int flag_array = 0;
                    int flag_parser = 0;
                    Map<Integer, String> involved_map_item = new HashMap<>(); // For the Map value.
                    for(int tainted_param_index : tainted_param_indices){
                        Value tainted_param = ie.getArg(tainted_param_index);
                        String tainted_param_type = tainted_param.getType().toString();
                        if(tainted_param_type.equals("android.content.res.TypedArray")){
                            flag_array = 1;
                        } else if(tainted_param_type.equals("android.content.res.XmlResourceParser")){
                            flag_parser = 1;
                        } else if(Utils.isMapValue(tainted_param)){
                            String tainted_map_item = mapValueToTaintedItem_path.get(tainted_param);
                            if(tainted_map_item!=null) {
                                involved_map_item.put(tainted_param_index, tainted_map_item);
                            }else{
                                Utils.printPartingLine("!");
                                System.out.println("Cannot find the tainted item of the Map value: " + data_structure);
                                Utils.printPartingLine("!");
                                exit(0);
                            }
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
                            updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, passing_variables, newValueToCopy_path, callee_name);
                            passing_unit.add(unit);
                            continue;
                        }
                    }
                    // The add / put method is related to a Map value.
                    // For a Map value, we need know whether the tainted position is the key or the value.
                    if ("add_addAll_put_putAll".contains(callee_name)) { // add(tainted_value), put(tainted_value)
                        if (base != null) {
                            // Update the Map value information.
                            if(Utils.isMapValue(base)){
                                String tainted_map_item = confirmTaintedItemOfTaintedMap(callee_name, ie, tainted_param_indices,
                                        passing_unit, mapValueToTaintedItem_path);
                                storeTaintedMapValueAndCorrespondingTaintedItem(base, tainted_map_item, mapValueToTaintedItem_path, newValueToCopy_path);
                            }
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, passing_variables, newValueToCopy_path, callee_name);
                            passing_unit.add(unit);
                            continue;
                        } else if(assignStmt == 1){
                            // Update the Map value information.
                            AssignStmt as = (AssignStmt) unit;
                            if(Utils.isMapValue(as.getLeftOp())){
                                String tainted_map_item = confirmTaintedItemOfTaintedMap(callee_name, ie, tainted_param_indices,
                                        passing_unit, mapValueToTaintedItem_path);
                                storeTaintedMapValueAndCorrespondingTaintedItem(as.getLeftOp(), tainted_map_item, mapValueToTaintedItem_path, newValueToCopy_path);
                            }
                        }
                    }
                    if(callee_name.equals("arraycopy")){
                        // Update the tainted value.
                        Value newly_tainted_value = ie.getArg(2);
                        updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, passing_variables, newValueToCopy_path, callee_name);
                        passing_unit.add(unit);
                        continue;
                    }
                    if(needRecordMethod(assignStmt, flag_parser, callee_name)){
                        String tainted_point_sig = tainted_param_indices + involved_map_item.toString() + element;
                        if((ie instanceof InterfaceInvokeExpr) && base!=null) { // For an Interface invoking, different bases may correspond to different implemented methods.
                            tainted_point_sig += unit;
                        } else { // There may have some different invoking statements that involve the same tainted method, parameters, and elements.
                            tainted_point_sig += callee.getSignature();
                        }
                        if(!recorded_tainted_points.contains(tainted_point_sig)) { // This tainted point has not been stored.
                            Log.logData(analysis_data, "--- Record the tainted method: " + callee_name);
                            recorded_tainted_points.add(tainted_point_sig);
                            // Store the tainted child.
                            BU tainted_child = new BU(callee, tainted_param_indices, element, unit, involved_map_item); // This element only related to entry method.
                            base_unit.storeTaintedChild(tainted_child);
                            // Record the newly tainted point.
                            String associated_element = getAssociatedElement(base_element, element); // This element related to entry method and its parents.
                            List<BU> parents = Utils.deepCopy(base_parents);
                            parents.add(base_unit);
                            BU new_tainted_point = new BU(callee, tainted_param_indices, associated_element, parents, unit, involved_map_item);
                            tainted_points.offer(new_tainted_point);
                        } else {
                            Log.logData(analysis_data, "--- This tainted method has been recoded.");
                        }
                    }
                    if(isTaintedAttribute(callee_name)){
                        flag_attribute = 1;
                    }
                } else {
                    // The tainted value is the base of an invoking.
                    if (base != null) {
                        if(unit instanceof InvokeStmt){
                            System.out.println("Special method: " + unit);
                        }
                        if (involved_entry_values.contains(base) || involved_pre_tainted_values.contains(base)) {
                            Log.logData(analysis_data, "--- Tainted base.");
                            if(canFilterForTaintedBase(base, callee_name)){
                                Log.logData(analysis_data, "--- Pass.");
                                continue;
                            }
                            if(isTaintedAttribute(base, callee_name)){
                                flag_attribute = 1;
                            }
                        }
                    }
                }

                // Pass the tainted value.
                if (assignStmt == 1) {
                    AssignStmt as = (AssignStmt) unit;
                    // There is a copy of entry value.
                    if(Utils.hasCopyOfValues(as, source_variables_path)){
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    if (ie == null) {
                        String right_op = as.getRightOp().toString();
                        if (right_op.startsWith("lengthof")) {
                            Log.logData(analysis_data, "--- Pass.");
                            continue;
                        }
                        if(isTaintedAttribute(as)){
                            flag_attribute = 1;
                        }
                    }
                    // Update the Map value information.
                    updateTaintedMapValueInfo(as, ie, passing_unit, mapValueToTaintedItem_path, newValueToCopy_path);
                    // Update the tainted value.
                    Value newly_tainted_value = as.getLeftOp();
                    if(newly_tainted_value.getType().toString().endsWith("ParsingPackage")){ // The obtained data structures are attributions of ParsingPackage.
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    if(flag_attribute == 1 || newly_tainted_value.getType().toString().equals("boolean")){
                        addNewlyTaintedValue(newly_tainted_value, passing_variables, newValueToCopy_path);
                        Log.logData(analysis_data, "--- Update the tainted value: " + passing_variables);
                    } else {
                        updateTaintedValues(newly_tainted_value, involved_pre_tainted_values, passing_variables, newValueToCopy_path, callee_name);
                    }
                }
                passing_unit.add(unit);
            }
        }

        // Store some information.
        Log.logData(analysis_data, Utils.generatePartingLine("="));
        Log.logData(analysis_data, "Store information -- analyze completely.");
        if(passing_variables.isEmpty()){
            passing_variables.add(null);
        }
        for(Value v : passing_variables) {
            data_structure = getDataStructure(v, mapValueToTaintedItem_path, valueToField_path, null, return_value, 0);
            base_unit.storeInnerElementAndStructure2(element, data_structure); // This element only related to the entry method.
            String associated_element = getAssociatedElement(base_element, element); // This element related to the entry method and its parents.
            storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
        }
    }

    public static void dataFlowAnalysisForMethod(BU entry){
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
        // Initialize the Map value information.
        List<Value> entry_values = entry.getTaintedValues();
        Map<Integer, String> entry_mapItem = entry.getTaintedMapItem();
        Map<Value, String> mapValueToTaintedItem = new HashMap<>();
        if(entry_values == null) {
            Set<Integer> entry_param_indices = entry.getTaintedParamIndices();
            entry_values = new ArrayList<>();
            for (int param_index : entry_param_indices) {
                Value parameter = Utils.getParameterOfMethod(body, param_index);
                if (parameter != null) {
                    entry_values.add(parameter);
                    if(entry_mapItem!=null && entry_mapItem.containsKey(param_index)){
                        mapValueToTaintedItem.put(parameter, entry_mapItem.get(param_index));
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
        }


        Log.logData(analysis_data, "+ Entry value: " + entry_values);
        Log.logData(analysis_data, "+ Entry element: " + entry.getOuterElement());
        Log.logData(analysis_data, "+ Entry map item: " + mapValueToTaintedItem);

        Utils.printPartingLine("=");
        System.out.println("+ Method: " + entry_method.getName());
        System.out.println("+ Entry value: " + entry_values);
        System.out.println("+ Entry element: " + entry.getOuterElement());
        System.out.println("+ Entry map item: " + entry_mapItem);

        // Construct the block graph.
        CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        Log.logBody(body);
        Log.logCBG(cbg);

        Map<Value, String> stringValueToLikelyElement = new HashMap<Value, String>(); // The Values whose concrete value is String.
        Map<Value, String> numericValueToConcreteAssignment = new HashMap<Value, String>(); // The concrete value of all numeric Values (iX, bX, zX).
        Map<Value, Value> newValueToCopy = new HashMap<Value, Value>(); // The newly constructed object and its copy.
        Map<Value, String> valueToField = new HashMap<>(); // The value related to a field.

        List<Value> entry_value_copies = Utils.deepCopy(entry_values);

        // To avoid path explosion caused by massive blocks, we start our analysis with the block we are interested in.
        // The general analysis method -- treats the element parser as a whole and gets its parse result.
        // The secondary analysis method -- gets the attributes of the element parser.
        // The special methods implement multiple analysis methods.
        boolean special_method = isSpecialMethod(entry_method.getName());
        if(special_method){
            transformEntryValue(entry_value_copies, body, true);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "Transform the entry value: " + entry_value_copies);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            System.out.println("Special method, Transform the entry value: " + entry_value_copies);
        }
        System.out.println("Find interested block ...");
        List<Block> interested_blocks = findAllInterestedBlocks(cbg, entry, entry_value_copies, entry.getEntryAssigns(), stringValueToLikelyElement);
        if(interested_blocks.isEmpty()){
            if(special_method){
                Utils.printPartingLine("!");
                System.out.println("Cannot find the interested block of the special method: " + entry_method.getSignature());
                Utils.printPartingLine("!");
                exit(0);
            }
            // These methods do not implement the general analysis methods.
            // We need transform the entry value.
            transformEntryValue(entry_value_copies, body, false);
            System.out.println("Cannot find the interested block, transform the entry value: " + entry_value_copies);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "Cannot find the interested block, transform the entry value :" + entry_value_copies);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            // Find the interested block again.
            interested_blocks = findAllInterestedBlocks(cbg, entry, entry_value_copies, entry.getEntryAssigns(), stringValueToLikelyElement);
            if(interested_blocks.isEmpty()){
                entry.storeInnerElementAndStructure2(null, null);
                Log.logData(analysis_data, "Still cannot find, this method does not need to be analyzed.");
                Utils.printPartingLine("!");
                System.out.println("Cannot find the interested block.");
                Utils.printPartingLine("!");
                return;
            }
        }
        int path_sensitive = 1;
        Block start_block;
        System.out.println("Find start block ... ");
        if(path_insensitive_methods.contains(entry_method.getName())){
            start_block = findStartBlock(cbg, entry, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment,
                    stringValueToLikelyElement, valueToField, mapValueToTaintedItem);
            path_sensitive = 0;
        } else {
            start_block = findStartBlock(interested_blocks, cbg, entry, entry_value_copies, newValueToCopy, numericValueToConcreteAssignment,
                    stringValueToLikelyElement, valueToField, mapValueToTaintedItem);
        }
        if(start_block == null) {
            Utils.printPartingLine("!");
            System.out.println("Cannot find the start block of the special method: " + entry_method.getSignature());
            Utils.printPartingLine("!");
            exit(0);
        }

        System.out.println("+ Start block id: " + start_block.getIndexInMethod());
        System.out.println("+ Parameters: " + entry.getParameters());
        System.out.println("+ numeric: " + numericValueToConcreteAssignment);
        System.out.println("+ likely_element: " + stringValueToLikelyElement);
        // Log data.
        Log.logData(analysis_data, "+ Parameters:" + entry.getParameters());
        Log.logData(analysis_data, "+ Start block id: " + start_block.getIndexInMethod());
        Log.logData(analysis_data, "+ likely_element: " + stringValueToLikelyElement);

        System.out.println("Generate path...");
        if(path_sensitive == 0){ // This method is unsuitable for the path-sensitive analysis.
            List<Integer> path = new ArrayList<>();
            for (int i = start_block.getIndexInMethod(); i < cbg.getBlocks().size(); i++) {
                path.add(i);
            }
            Graph.paths.add(path);
            path_sensitive = 0;
        } else {
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
            dataFlowAnalysisForBlocks(cbg.getBlocks(), path, path_sensitive, entry, entry_value_copies, newValueToCopy,
                    numericValueToConcreteAssignment, mapValueToTaintedItem, recorded_tainted_points,
                    stringValueToLikelyElement, valueToField);
            path_num+=1;
            if(path_num == total_num || path_num % 1000 == 0) {
                System.out.println("Analyzed path num: " + path_num);
            }
            //Utils.pause();
        }
    }

    // Find the method for starting to parse the AndroidManifest.xml
    public static void findEntryPoints() {
        List<SootMethod> methods = Utils.getMethodsOfClass(parsing_class);
        for (SootMethod sm : methods) {
            if (sm.isConcrete()) {
                Body body = sm.retrieveActiveBody();
                List<Value> entry_values = new ArrayList<>();
                Set<AssignStmt> entry_assigns = new HashSet<>();
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
                                            Value entry_value = as.getLeftOp();
                                            if (!entry_values.contains(entry_value)) {
                                                entry_values.add(entry_value);
                                            }
                                            entry_assigns.add(as);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if(!entry_values.isEmpty()){
                    BU entry = new BU(sm, entry_values);
                    entry.setEntryAssigns(entry_assigns);
                    tainted_points.offer(entry);
                }
            }
        }
    }

    public static void findSuspiciousDataStructures(){
        Log.deleteData(element_data);
        Log.deleteData(method_data);
        Log.deleteData(analysis_data);
        Log.deleteData(suspicious_structures);
        Log.deleteData(pkg_structures);


        String[] skip_nms = {"\"android\"", "\"array\"", "\"singleInstancePerTask\""};
        String[] skip_mds = {"append", "obtainAttributes", "skipCurrentTag", "unknownTag", "size", "byteSizeOf", "forEachPackage", "recycle"};
        String[] skip_cls = {"android.content.res.XmlResourceParser", "android.content.pm.parsing.result.ParseInput",
                "com.android.internal.util.AnnotationValidations", "android.util.Slog"};
        String[] pims = {"parseData"};
        skip_names.addAll(new ArrayList<>(Arrays.asList(skip_nms)));
        skip_methods.addAll(new ArrayList<>(Arrays.asList(skip_mds)));
        skip_classes.addAll(new ArrayList<>(Arrays.asList(skip_cls)));
        path_insensitive_methods.addAll(new ArrayList<>(Arrays.asList(pims)));

        findEntryPoints();

        List<BU> analyzed_tainted_points = new ArrayList<>();

        while (!tainted_points.isEmpty()) {
            BU tainted_point = tainted_points.poll();
            SootMethod tainted_method = tainted_point.getMethod();
            String tainted_element = tainted_point.getOuterElement();
            Unit tainted_call_unit = tainted_point.getCallUnit();

            Log.logData(analysis_data, Utils.generatePartingLine("#"));
            Log.logData(analysis_data, "+ Analyzed method: " + tainted_method);

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

            int flag_analyzed = 0;
            String tainted_point_sig = generateTaintedPointSignature(tainted_point);
            for(BU atp : analyzed_tainted_points){
                String atp_sig = generateTaintedPointSignature(atp);
                if(atp_sig.equals(tainted_point_sig)){
                    Log.logData(analysis_data, "+ Entry value: " + tainted_point.getTaintedValues());
                    Log.logData(analysis_data, "+ Entry paramIndices: " + tainted_point.getTaintedParamIndices());
                    Log.logData(analysis_data, "This method has been analyzed.");
                    /*Utils.printPartingLine("=");
                    System.out.println("+ Method: " + tainted_method.getName());
                    System.out.println("+ Entry value: " + tainted_point.getTaintedValues());
                    System.out.println("+ Entry parameters: " + tainted_point.getTaintedParamIndices());
                    System.out.println("+ Analyzed.");*/
                    flag_analyzed = 1; // This tainted method has been analyzed.
                    tainted_point.setParameters(atp.getParameters()); // The same tainted methods have the same parameters.
                    List<Pair<String, String>> e_ds = atp.getInnerElementAndStructures();
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
                    Set<BU> children = atp.getTaintedChildren();
                    tainted_point.setTaintedChildren(children); // The same tainted methods have the same tainted children.
                    if(children != null) {
                        List<BU> parents = Utils.deepCopy(tainted_point.getParents());
                        parents.add(tainted_point);
                        for (BU child : children) {
                            String element = child.getOuterElement(); // This element only associate with the tainted method.
                            String associated_element = getAssociatedElement(tainted_element, element); // This element associate with the tainted method and its parents.
                            BU newly_tainted_point = new BU(child.getMethod(), child.getTaintedParamIndices(), associated_element, parents, child.getCallUnit(), child.getTaintedMapItem());
                            tainted_points.offer(newly_tainted_point);
                        }
                    }
                    break;
                }
            }

            if(flag_analyzed==1) {
                analyzed_tainted_points.add(tainted_point);
                continue;
            }

            analyzed_tainted_points.add(tainted_point);
            dataFlowAnalysisForMethod(tainted_point);

            //Utils.pause();
            //sleep(2000);
        }
        Utils.printPartingLine("=");
        for(Map.Entry<String, Set<String>> entry: associatedElementToDataStructures.entrySet()){
            String associated_element = entry.getKey();
            Log.logData(element_data, Utils.generatePartingLine("="));
            Log.logData(element_data, "+ associated element: " + associated_element);
            String out = entry.getKey()+",";
            for(String ds : entry.getValue()){
                if(ds!= null && ds.contains("unknown")){
                    System.out.println("==== " + ds);
                    ds = transformUnknownTaintedMapItem(ds, analyzed_tainted_points);
                    System.out.println("==== " + ds);
                }
                Log.logData(element_data, Utils.generatePartingLine("*"));
                Log.logData(element_data, "+ data structure: " + ds);
                out += ds + ",";
                if(ds!=null && ds.contains("<") && ds.contains(parsedPackage_settings_class)){
                    Log.logData(pkg_structures, ds + "=>" + associated_element);
                }
                // We only care about the field in the ParsingPackageImpl class,
                // because other classes who want to get a package's settings must through this class.
                if(isSuspiciousDataStructure(ds)){
                    Log.logData(suspicious_structures, ds + "=>" + associated_element);
                    for (BU point : analyzed_tainted_points) {
                        List<Pair<String, String>> e_ds = point.getInnerElementAndStructures();
                        for (Pair<String, String> e_d : e_ds) {
                            String element = getAssociatedElement(point.getOuterElement(), e_d.getO1());
                            if (associated_element.equals(element) && ds.equals(e_d.getO2())) {
                                Log.logData(element_data, Utils.generatePartingLine("-"));
                                Log.logData(element_data, "+ call path:");
                                for (BU parent : point.getParents()) {
                                    Log.logData(element_data, "--- " + parent.getMethod().getSignature());
                                }
                                Log.logData(element_data, "---" + point.getMethod().getSignature());
                            }
                        }
                    }
                }
            }
            System.out.println(out);
        }
    }
}
