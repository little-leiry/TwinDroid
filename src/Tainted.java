import soot.*;
import soot.jimple.*;
import soot.jimple.internal.ConditionExprBox;
import soot.jimple.spark.ondemand.pautil.SootUtil;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.scalar.Pair;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.util.*;

import static java.lang.System.exit;

public class Tainted {
    private SootMethod mMethod;
    private Value mValue;
    private String mElement;
    private List<SootMethod> mParents;
    private Unit mStartUnit;
    // The tainted_methods needed to be analysed.
    // Each object consists of <tainted method, tainted value, associated element>
    // Use queue to do BFS.
    public static Queue<Tainted> tainted_points = new LinkedList<Tainted>();

    // element name => data structures.
    public static Map<String, Set<Value>> associatedElementToDataStructures = new HashMap<String, Set<Value>>();
    // method => list of <child, associated element>
    public static Map<SootMethod, Set<Tainted>> methodToTaintedChildren = new HashMap<SootMethod, Set<Tainted>>();

    // method => List of Pair<element name, data structure>
    public static Map<Tainted, Set<Pair<String, Value>>> taintedPointToElementAndDataStructures = new HashMap<Tainted, Set<Pair<String, Value>>>();

    public static final String element_data = "logs/element_data.txt";
    public static final String method_data = "logs/method_data.txt";

    public static final String analysis_data = "logs/analysis_data.txt";

    public Tainted(SootMethod method, Value value, String element, List<SootMethod> parents) {
        mMethod = method;
        mValue = value;
        mElement = element;
        mParents = parents;
    }

    public Tainted(SootMethod method, Value value, String element){
        mMethod = method;
        mValue = value;
        mElement = element;
    }

    public Tainted(SootMethod method, Value value, Unit start){
        mMethod = method;
        mValue = value;
        mStartUnit = start;
    }

    public SootMethod getMethod(){
        return mMethod;
    }

    public Value getValue(){
        return mValue;
    }

    public String getElement(){
        return mElement;
    }

    public List<SootMethod> getParents(){
        return mParents;
    }

    public Unit getStartUnit(){
        return mStartUnit;
    }
    public void setParent(List<SootMethod> parents){
        mParents = parents;
    }

    // The return element is only related to the current analyze method.
    public static String getElement(String element, List<String> elements){
        if(element!=null) return element;
        if(elements!=null) return elements.toString();
        return null;
    }

    // The return element is related to the current analyze method and its parents.
    public static String getAssociatedElement(String entry_element, String element){
        if(entry_element == null){
            return element;
        }else if(element == null) {
            return entry_element;
        } else {
            return entry_element + "_" + element;
        }
    }

    public static List<String> getElementsOfUnit(Unit unit, Map<String, Unit> elementToUnit) {
        if (elementToUnit.containsValue(unit)) {
            List<String> elements = new ArrayList<>(); //One method may correspond to multiple elements.
            for (Map.Entry<String, Unit> entry : elementToUnit.entrySet()) {
                if (unit.equals(entry.getValue())) {
                    elements.add(entry.getKey());
                }
            }
            return elements;
        }
        return null;
    }

    // associated element: related to the current analyzed method and its parents.
    public static void storeAssociatedElementAndCorrespondingDataStructure(SootMethod entry_method, List<SootMethod> entry_parents, String associated_element, Value data_structure) {
        if(associated_element==null) return;
        String structure;
        if (data_structure == null){
            return;
        } else if (data_structure.getType().toString().endsWith("parsing.result.ParseResult")){ // The parse result of this element has not been solved completely.
            return;
        } else if (data_structure.toString().contains(".<")) {
            structure = data_structure.toString();
        } else {
            structure = data_structure.getType().toString();
        }

        Set<Value> ds = associatedElementToDataStructures.get(associated_element);
        if (ds == null) { // This key does not exist.
            ds = new HashSet<>();
            ds.add(data_structure);
            associatedElementToDataStructures.put(associated_element, ds);
            // Log data.
            Log.logData(element_data, Utils.generatePartingLine("="));
            Log.logData(element_data, "+ associated element: " + associated_element);
            Log.logData(element_data, "+ data structure: " + structure);
            Log.logData(element_data, "+ call path:");
            List<SootMethod> methods = Utils.deepCopy(entry_parents);
            methods.add(entry_method);
            for(SootMethod m : methods){
                Log.logData(element_data, "-- " + m.getSignature());
            }
        } else {
            if(!ds.contains(data_structure)) { // Avoid duplicated logs.
                ds.add(data_structure);
                // Log data.
                Log.logData(element_data, Utils.generatePartingLine("="));
                Log.logData(element_data, "+ associated element: " + associated_element);
                Log.logData(element_data, "+ data structure: " + structure);
                Log.logData(element_data, "+ call path:");
                List<SootMethod> methods = Utils.deepCopy(entry_parents);
                methods.add(entry_method);
                for(SootMethod m : methods){
                    Log.logData(element_data, "-- " + m.getSignature());
                }
            }
        }
    }

    // element: only related to the current analyzed method.
    public static void storeTaintedPointAndCorrespondingElementAndDataStructure(Tainted tainted_point, String element, Value data_structure) {
        String s = element;
        if(element == null){
            s = "NULL";
        }
        String structure;
        if (data_structure == null){
            structure = "NULL";
        } else if (data_structure.toString().contains(".<")) {
            structure = data_structure.toString();
        } else {
            structure = data_structure.getType().toString();
        }

        Log.logData(analysis_data, Utils.generatePartingLine("~"));
        Log.logData(analysis_data, "- Element: " + s);
        Log.logData(analysis_data, "- Data structure: " + structure);
        Log.logData(analysis_data, Utils.generatePartingLine("~"));

        Set<Pair<String, Value>> e_ds = taintedPointToElementAndDataStructures.get(tainted_point);
        Pair<String, Value> e_d = new Pair<String, Value>(element, data_structure);
        if (e_ds == null) { // This key does not exist.
            e_ds = new HashSet<>();
            e_ds.add(e_d);
            taintedPointToElementAndDataStructures.put(tainted_point, e_ds);
            // Log.
            Log.logData(method_data, Utils.generatePartingLine("="));
            Log.logData(method_data, "+ Element: " + s);
            Log.logData(method_data, "+ Data structure: " + structure);
        } else {
            if(!e_ds.contains(e_d)) { // Avoid duplicated logs.
                e_ds.add(e_d);
                // Log data.
                Log.logData(method_data, Utils.generatePartingLine("="));
                Log.logData(method_data, "+ Element: " + s);
                Log.logData(method_data, "+ Data structure: " + structure);
                //Log.logData(method_data, Utils.generatePartingLine("-"));
            }
        }
    }

    public static void storeMethodAndCorrespondingTaintedChildren(SootMethod method, Tainted child){
        Set<Tainted> children = methodToTaintedChildren.get(method);
        if(children==null){
            children=new HashSet<>();
            children.add(child);
            methodToTaintedChildren.put(method, children);
        } else {
            children.add(child);
        }
    }

    public static int storeValueAndCorrespondingLikelyElement(AssignStmt as, Map<Value, String> valueToLikelyElement){
        List<ValueBox> vbs = as.getUseBoxes();
        if (vbs.size()==1 && vbs.get(0).getValue() instanceof StringConstant) {
            Value element_value = as.getLeftOp();
            String likely_element = as.getUseBoxes().get(0).getValue().toString();
            if(likely_element.startsWith("\"/")) return 1;
            valueToLikelyElement.put(element_value, likely_element);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "Likely element: " + as);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            return 0;
        }
        return 1;
    }

    public static int storeNumericValueAndCorrespondingConcreteAssignment(AssignStmt as, Map<Value, String> numericValueToConcreteAssignment){
        Value def_value = as.getLeftOp();
        if(def_value.toString().contains(".<")) return 1;
        List<ValueBox> vbs = as.getUseBoxes();
        if("int_byte_boolean".contains(def_value.getType().toString())){
            if(vbs.size() == 1){
                Value use_value = as.getRightOp();
                if(use_value instanceof IntConstant){ // Concrete assignment.
                    numericValueToConcreteAssignment.put(def_value, use_value.toString());
                } else {
                    String assign = numericValueToConcreteAssignment.get(use_value);
                    numericValueToConcreteAssignment.put(def_value, assign);
                }
            } else {
                String s = vbs.get(0).getValue().toString();
                // Compute the concrete value when the assignment is an express.
                // Replace the Value with its concrete assignment.
                // Sort the list according to the Value name's length first in case that one value name is the prefix of another Value name.
                if(Utils.isExpress(s)) {
                    Collections.sort(vbs, new VBComparator());
                    int flag_compute = 1;
                    for (int j = 1; j < vbs.size(); j++) {
                        Value v = vbs.get(j).getValue();
                        String assign = numericValueToConcreteAssignment.get(v);
                        if (assign == null) {
                            flag_compute = 0; // Cannot compute the value of this express because the concrete value of the numeric Value is unknown.
                            numericValueToConcreteAssignment.put(def_value, null);
                            break;
                        }
                        s = s.replace(v.toString(), assign);
                    }
                    if (flag_compute == 1) {
                        ScriptEngineManager sem = new ScriptEngineManager();
                        ScriptEngine se = sem.getEngineByName("js");
                        try {
                            Object result = se.eval(s);
                            numericValueToConcreteAssignment.put(def_value, result.toString());
                        } catch (ScriptException e) {
                            Log.logData(analysis_data, Utils.generatePartingLine("!"));
                            Log.logData(analysis_data, "Computing Error: " + s);
                            Log.logData(analysis_data, Utils.generatePartingLine("!"));
                            throw new RuntimeException(e);
                        }
                    }
                } else if (vbs.size() == 2){
                    // The assignment involves data transformation.
                    if(s.startsWith("(")){
                        String assign = numericValueToConcreteAssignment.get(vbs.get(1).getValue());
                        numericValueToConcreteAssignment.put(def_value, assign);
                    } else {
                        numericValueToConcreteAssignment.put(def_value, null);
                    }
                } else {
                    numericValueToConcreteAssignment.put(def_value, null);
                }
            }
            return 0;
        }
        return 1;
    }

    public static String isRelatedToElement(InvokeExpr ie, Map<Value, String> valueToLikelyElement){
        if(ie == null) return null;

        String method_name = ie.getMethod().getName();
        Value base = Utils.getBaseOfInvokeExpr(ie);

        if (method_name.equals("equals")) {
            if (ie.getArg(0) instanceof StringConstant) { // parser.getName().equals(element)
                String s = ie.getArg(0).toString();
                if (!SkipInfo.skip_names.contains(s)) {
                    return s;
                }
            } else if (base != null && valueToLikelyElement!=null) { // element.equals(parser.getName())
                if (valueToLikelyElement.containsKey(base)) {
                    String s = valueToLikelyElement.get(base);
                    if (!SkipInfo.skip_names.contains(s)) {
                        return s;
                    }
                }
            }
        }
        return null;
    }

    public static boolean isInterestedUnit(Unit unit, List<Value> entry_value_copies, Map<Value, String> valueToLikelyElement){
        if(unit instanceof AssignStmt){
            AssignStmt as =(AssignStmt) unit;
            InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
            Value base = Utils.getBaseOfInvokeExpr(ie);

            if(entry_value_copies.contains(base)){
                // Interested unit -- Type transformation of the entry value.
                if(ie.getMethod().getName().startsWith("to")){
                    return true;
                }
                // Interested unit -- Get result from entry value (when the entry value's type is ParseResult).
                if (base.getType().toString().endsWith("parsing.result.ParseResult")) {
                    if (ie.getMethod().getName().equals("getResult")) { // ! result.getResult()
                        return true;
                    }
                }
            }
            // Interested unit -- Pass in the entry value as a parameter.
            if(Utils.hasParameterOfInvokeStmt(ie, entry_value_copies) != -1) {
                String method_name = ie.getMethod().getName();
                String declaring_class;
                if (base != null) {
                    declaring_class = ((RefType) base.getType()).getSootClass().getName();
                } else {
                    declaring_class = ie.getMethod().getDeclaringClass().getName();
                }
                if (!SkipInfo.skip_methods.contains(method_name) && !SkipInfo.skip_classes.contains(declaring_class)) { // Filter uninterested methods and classes.
                    return true;
                }
            }
            // Interested unit -- Related to elements.
            if(isRelatedToElement(ie, valueToLikelyElement)!=null){
                return true;
            }
        } else if (unit instanceof InvokeExpr) {
            InvokeExpr ie = (InvokeExpr) unit;
            Value base = Utils.getBaseOfInvokeExpr(ie);
            // Interested unit -- Pass in the entry value as a parameter.
            if(Utils.hasParameterOfInvokeStmt(ie, entry_value_copies) != -1) {
                String method_name = ie.getMethod().getName();
                String declaring_class;
                if (base != null) {
                    declaring_class = ((RefType) base.getType()).getSootClass().getName();
                } else {
                    declaring_class = ie.getMethod().getDeclaringClass().getName();
                }
                if (!SkipInfo.skip_methods.contains(method_name) && !SkipInfo.skip_classes.contains(declaring_class)) { // Filter uninterested methods and classes.
                    return true;
                }
            }
        }
        return false;
    }

    public static void storeUsefulInfo(AssignStmt as, List<Value> entry_value_copies, int flag_case, Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToLikelyElement){
        if(as==null) return;

        if (Utils.isCopyOfValues(as, entry_value_copies)) {
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Log.logData(analysis_data, "--- Copy entry value: " + as);
            Log.logData(analysis_data, Utils.generatePartingLine("+"));
            Value copy = as.getLeftOp();
            if(!entry_value_copies.contains(copy)) {
                entry_value_copies.add(as.getLeftOp());
            }
        }
        if (flag_case == 1) {
            storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment);
        }
        storeValueAndCorrespondingLikelyElement(as, valueToLikelyElement);
    }

    public static Block findStartBlock(CompleteBlockGraph cbg, List<Value> entry_value_copies, int flag_case, Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToLikelyElement){
        Block start_block = null;

        for(Block block : cbg.getBlocks()){
            for(Unit unit : block){
                if(isInterestedUnit(unit, entry_value_copies, valueToLikelyElement)){
                    System.out.println("Interested unit: " + unit);
                    start_block = block;
                    break;
                }
                if(unit instanceof AssignStmt) {
                    AssignStmt as = (AssignStmt) unit;
                    // Store useful information.
                    storeUsefulInfo(as, entry_value_copies, flag_case, numericValueToConcreteAssignment, valueToLikelyElement);
                }else if (unit instanceof SwitchStmt){
                    // For switch-case statement, we need to analyze each case.
                    SwitchStmt ss = (SwitchStmt) unit;
                    for (int i = 0; i < ss.getTargets().size(); i++) {
                        Unit u = ss.getTarget(i);
                        if(isInterestedUnit(u, entry_value_copies, valueToLikelyElement)){
                            System.out.println("Interested unit: " + unit);
                            start_block = block;
                            break;
                        }
                    }
                    if(start_block!=null) break;
                }
            }
            if(start_block != null) break;
        }
        return start_block;
    }

    public static void findEntryPoints() {
        String className = "android.content.pm.parsing.ParsingPackageUtils"; // the class for parsing an apk
        List<SootMethod> methods = Utils.getMethodsOfClass(className);
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
                                            Value entry_value = as.getLeftOp();
                                            tainted_points.offer(new Tainted(sm, entry_value, body.getUnits().getSuccOf(unit)));
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
    public static void dataFlowAnalysisForBlocks(List<Block> blocks, List<Integer> block_ids, Tainted entry, List<Value> entry_value_copies, int flag_case, int flag_start,
                                                 Map<Value, String> numericValueToConcreteAssignment, Set<Integer> skip_block_ids, List<SootMethod> stored_methods,
                                                 Set<Unit> target_units, Map<Value, String> valueToLikelyElement) {

        SootMethod entry_method = entry.getMethod();
        String entry_element = entry.getElement();
        Unit start_unit = entry.getStartUnit();
        List<SootMethod> entry_parents = entry.getParents();

        // Copy the map.
        // Specific to this path.
        Map<Value, String> numericValueToConcreteAssignment_path = Utils.deepCopy(numericValueToConcreteAssignment);
        Map<Value, String> valueToLikelyElement_path = Utils.deepCopy(valueToLikelyElement);

        Value case_value = null; // The bridge value between two LookupSwithStmts.
        String element = null; // This element only related to entry method.

        Value data_structure;
        Value tainted_value = null;
        int pass_tainted_value = 1; // Flag that the current tainted value can be updated.

        for (int i = 0; i< block_ids.size(); i++) {
            int block_id = block_ids.get(i);
            Block block = blocks.get(block_id);
            int flag_skip = 1;
            for (Unit unit : block) {
                if(flag_start == 0){ // Analysis should start with the start unit.
                    if (start_unit.equals(unit)) {
                        flag_start = 1;
                    }
                }
                if (flag_start == 0){
                    // Store useful information before we skip the unit.
                    if(unit instanceof AssignStmt){
                        AssignStmt as = (AssignStmt) unit;
                        storeUsefulInfo(as, entry_value_copies, flag_case, numericValueToConcreteAssignment_path, valueToLikelyElement_path);
                    }
                    continue;
                }

                // Cannot skip a target block;
                if(flag_skip == 1 && target_units.contains(block.getHead())){
                    // System.out.println(block.getHead());
                    // System.out.println(block_id);
                    flag_skip = 0;
                }

                InvokeExpr ie = null;
                Value base = null;
                SootMethod callee = null;
                String callee_name = "NULL";
                String declaring_class = "NULL";

                int need_analysis = 0;
                int assignStmt = 0;
                int flag_entry = 0; // Flag that this unit whether contains the entry value.

                if(unit instanceof TableSwitchStmt){
                    Utils.printPartingLine("!");
                    System.out.println("Find the TableSwitchStmt.");
                    Utils.printPartingLine("!");
                    exit(0);
                }

                if(flag_case == 1) {
                    // Get the mapping relationship of elements and methods.
                    // For the switch-case situation:
                    // switch(element)-case(XXX)=>parseXXX(parser):
                    // LookupSwitchStmt($i1){case -12356 goto z0 = equals(XXX), b2 = 0}
                    // LookupSwitchStmt(b2){case 0 goto $r6 = parseXXX(parser)}
                    if (unit instanceof LookupSwitchStmt) {
                        flag_skip = 0;
                        LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                        if (case_value == null) { // Get the bridge case value between two LookupSwitchStmts.
                            Unit default_unit = lss.getDefaultTarget();
                            if (default_unit instanceof GotoStmt) {
                                GotoStmt gs = (GotoStmt) default_unit;
                                if (gs.getTarget() instanceof AssignStmt) {
                                    AssignStmt as = (AssignStmt) gs.getTarget();
                                    case_value = as.getLeftOp();
                                    continue;
                                }
                            }
                        }
                        // Filter wrong paths.
                        if (case_value != null && lss.getUseBoxes().get(0).getValue().equals(case_value)) {
                            target_units.addAll(Utils.deepCopy(lss.getTargets()));
                            target_units.add(lss.getDefaultTarget());
                            String case_id = numericValueToConcreteAssignment_path.get(case_value); // Find the case id associated with this path.
                            if (case_id != null) {
                                int id = Integer.parseInt(case_id);
                                Unit target_unit;
                                if (id != -1) {
                                    target_unit = lss.getTarget(id);
                                } else {
                                    target_unit = lss.getDefaultTarget();
                                }
                                if (target_unit != null) {
                                    if(i + 1 < block_ids.size()) {
                                        Unit next_block_head = blocks.get(block_ids.get(i + 1)).getHead();
                                        Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                        Log.logData(analysis_data, "Case value: " + case_value + " => " + case_id);
                                        Log.logData(analysis_data, "Target unit: " + target_unit);
                                        Log.logData(analysis_data, "Next block head: " + next_block_head);
                                        Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                        // If the next block's first Unit is not the target Unit, this path is incorrect.
                                        if (!next_block_head.equals(target_unit)) {
                                            Utils.generatePartingLine("!");
                                            Log.logData(analysis_data, "Wrong path, stop analyzing!");
                                            Utils.generatePartingLine("!");
                                            return;
                                        }
                                    } else {
                                        Log.logData(analysis_data, Utils.generatePartingLine("!"));
                                        Log.logData(analysis_data, "Special path, the end block contains LookupSwitchStmt.");
                                        Log.logData(analysis_data, block_ids.toString());
                                        Log.logData(analysis_data, Utils.generatePartingLine("!"));
                                    }
                                } else {
                                    Utils.generatePartingLine("!");
                                    System.out.println("Cannot find the target Unit of the case ID [ " + case_id + " ].");
                                    System.out.println("SwitchStmt: " + lss);
                                    System.out.println("Method: " + entry_method.getSignature());
                                    Utils.generatePartingLine("!");
                                    exit(0);
                                }
                                // Finish transformation, reset the case value.
                                case_value = null;
                            } else {
                                Utils.generatePartingLine("!");
                                System.out.println("Cannot find the corresponding case ID of the case value [ " + case_value + " ].");
                                System.out.println("Method: " + entry_method.getSignature());
                                Utils.generatePartingLine("!");
                                exit(0);
                            }
                        }
                        continue;
                    }
                }

                // Filter wrong paths.
                if(unit instanceof IfStmt){
                    flag_skip = 0;
                    IfStmt is = (IfStmt) unit;
                    // Judge whether the condition is met.
                    // Replace the Value with its concrete assignment.
                    // Sort the list according to the Value name's length first in case that one value name is the prefix of another Value name.
                    String condition = is.getCondition().toString();
                    List<ValueBox> vbs = is.getUseBoxes();
                    Collections.sort(vbs, new VBComparator());
                    int flag_compute = 1;
                    for(ValueBox vb : vbs){
                        if( vb instanceof ConditionExprBox) continue;
                        Value v = vb.getValue();
                        if(v instanceof IntConstant) continue;
                        if("int_byte_boolean".contains(vb.getValue().getType().toString())){
                            String assign = numericValueToConcreteAssignment_path.get(v);
                            if(assign==null) {
                                flag_compute = 0;
                                break;
                            } else {
                                condition = condition.replace(v.toString(), assign);
                            }
                        } else {
                            flag_compute = 0;
                        }
                    }
                    if (flag_compute == 1) {
                        Unit target_unit = is.getTarget();
                        if(target_unit==null){
                            Utils.generatePartingLine("!");
                            System.out.println("Cannot find the target Unit of the IfStmt: " + is);
                            System.out.println("Method: " + entry_method.getSignature());
                            Utils.generatePartingLine("!");
                            exit(0);
                        }
                        //System.out.println(is);
                        //System.out.println(condition);
                        target_units.add(target_unit);
                        ScriptEngineManager sem = new ScriptEngineManager();
                        ScriptEngine se = sem.getEngineByName("js");
                        try {
                            boolean result = (boolean) se.eval(condition);
                            if(i + 1 <block_ids.size()) {
                                if (result) {
                                    // When the condition is met, if the next block's first Unit is not the target Unit, this path is incorrect.
                                    if (!blocks.get(block_ids.get(i + 1)).getHead().equals(target_unit)) {
                                        Log.logData(analysis_data, "--- Wrong path, stop analyzing!");
                                        return;
                                    }
                                } else {
                                    // When the condition is not met, if the next block's first Unit is the target Unit, this path is incorrect.
                                    if (blocks.get(block_ids.get(i + 1)).getHead().equals(target_unit)) {
                                        Utils.generatePartingLine("!");
                                        Log.logData(analysis_data, "Wrong path, stop analyzing!");
                                        Utils.generatePartingLine("!");
                                        return;
                                    }
                                }
                            } else {
                                Log.logData(analysis_data, Utils.generatePartingLine("!"));
                                Log.logData(analysis_data, "Special path, the end block contains IfStmt.");
                                Log.logData(analysis_data, block_ids.toString());
                                Log.logData(analysis_data, Utils.generatePartingLine("!"));
                            }
                        } catch (ScriptException e) {
                            Utils.generatePartingLine("!");
                            System.out.println("Computing Error: " + condition);
                            System.out.println(is);
                            Utils.generatePartingLine("!");
                            throw new RuntimeException(e);
                        }
                    }
                    continue;
                }

                // A statement needs to be analysed only if it contains the entry / tainted value.
                if (unit instanceof AssignStmt) {
                    assignStmt = 1;
                    AssignStmt as = (AssignStmt) unit;
                    ie = Utils.getInvokeOfAssignStmt(as);
                    if (Utils.hasRightValueOfAssignStmt(as, entry_value_copies)) {
                        flag_entry = 1;
                        need_analysis = 1;
                    } else if (Utils.isRightValueOfAssignStmt(as, tainted_value)) {
                        need_analysis = 1;
                    }
                    // This entry / tainted value has been re-defined.
                    if (need_analysis == 0) {
                        int index = Utils.hasLeftValueOfAssignStmt(as, entry_value_copies);
                        if (index!=-1) {
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(analysis_data, "+ Utils: " + as);
                            Log.logData(analysis_data, "--- The entry value [ " + entry_value_copies.get(index) + " ] is re-defined.");
                            Log.logData(analysis_data, "--- Remove this entry value.");
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            entry_value_copies.remove(index);
                        } else if (Utils.isLeftValueOfAssignStmt(as, tainted_value)) {
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(analysis_data, "+ Utils: " + as);
                            Log.logData(analysis_data,"--- The tainted value [ " + tainted_value + " ] is re-defined.");
                            data_structure = tainted_value; // Store some information when the tainted value is redefined.
                            tainted_value = null;
                            Log.logData(analysis_data, "--- Reset the tainted value: " + tainted_value);
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(analysis_data, "Store the information -- value re-defined.");
                            storeTaintedPointAndCorrespondingElementAndDataStructure(entry, element, data_structure); // This element only related to the entry method.
                            String associated_element = getAssociatedElement(entry_element, element); // This element related to the entry method and its parents.
                            storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure);
                            pass_tainted_value = 1;
                        }
                    }
                    // This statement is likely related to an element.
                    flag_skip &= storeValueAndCorrespondingLikelyElement(as, valueToLikelyElement_path);
                    if(flag_case == 1) {
                        // Store the byte value's concrete assignment.
                        // For the case ID transform of the two associated switch-case statements.
                        flag_skip &= storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment_path);
                    }
                } else if (unit instanceof InvokeStmt) {
                    ie = ((InvokeStmt) unit).getInvokeExpr();
                    if (Utils.hasParameterOfInvokeStmt(ie, entry_value_copies) != -1 || Utils.isParameterOfInvokeStmt(ie, tainted_value) != -1) {
                        need_analysis = 1;
                    }
                }

                if (ie != null) {
                    callee = ie.getMethod();
                    callee_name = callee.getName();
                    base = Utils.getBaseOfInvokeExpr(ie);
                }

                // Get the element's name.
                String s = isRelatedToElement(ie, valueToLikelyElement_path);
                if (s != null){
                    flag_skip = 0;
                    String old_element = element;
                    if(old_element != null) { // Have solved one element case.
                        // Store some information before updating the element.
                        Log.logData(analysis_data, Utils.generatePartingLine("="));
                        Log.logData(analysis_data, "Store information -- element update.");
                        data_structure = tainted_value;
                        tainted_value = null;
                        String e = old_element; // This element only related to the entry method.
                        storeTaintedPointAndCorrespondingElementAndDataStructure(entry, e, data_structure);
                        String associated_element = getAssociatedElement(entry_element, e); // This element related to the entry method and its parents.
                        storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure);
                        pass_tainted_value = 1;
                    }
                    // Update the element.
                    element = s;
                    Log.logData(analysis_data, Utils.generatePartingLine("+"));
                    Log.logData(analysis_data, "Element: " + element);
                    Log.logData(analysis_data, Utils.generatePartingLine("+"));
                    continue;
                }

                if (need_analysis == 0) continue;

                Log.logData(analysis_data, Utils.generatePartingLine("*"));
                Log.logData(analysis_data, "+ Unit: " + unit);
                if (flag_entry == 1) {
                    Log.logData(analysis_data, "--- Tainted by the entry value.");
                }
                Log.logData(analysis_data, "--- Tainted value: " + tainted_value);
                //Utils.printPartingLine("*");

                // Treat the tainted / entry value as a whole, ignore the part (ie., the attribution) of it.
                if (base != null) {
                    String base_type = base.getType().toString();
                    if (base.equals(tainted_value) || entry_value_copies.contains(base)) {
                        //Utils.printPartingLine("-");
                        Log.logData(analysis_data, "--- Tainted base.");
                        //Utils.printPartingLine("-");
                        if (base_type.endsWith("parsing.result.ParseResult")) {
                            if (!callee_name.equals("getResult")) { // ! result.getResult()
                                Log.logData(analysis_data, "--- Pass.");
                                continue;
                            } else {
                                pass_tainted_value = 1;
                            }
                        } else {
                            if (!callee_name.startsWith("to")) { // ! tainted_value.toBundle()
                                Log.logData(analysis_data, "--- Pass.");
                                continue;
                            }
                        }
                    }
                }

                // If the tainted / entry value is passed in the callee, this callee is tainted.
                Integer parameter_index = -1;
                parameter_index = Utils.hasParameterOfInvokeStmt(ie, entry_value_copies);
                if (parameter_index == -1) {
                    parameter_index = Utils.isParameterOfInvokeStmt(ie, tainted_value);
                }
                if (parameter_index != -1) {
                    //Utils.printPartingLine("-");
                    Log.logData(analysis_data, "--- Tainted callee.");
                    //Utils.printPartingLine("-");
                    if (callee_name.equals("add") || callee_name.equals("put")) { // xxx.add(tainted_value)
                        if (base != null) {
                            tainted_value = base;
                            Log.logData(analysis_data, "--- Pass.");
                            continue;
                        }
                    }
                    if (base != null) {
                        declaring_class = ((RefType) base.getType()).getSootClass().getName();
                    } else {
                        declaring_class = callee.getDeclaringClass().getName();
                    }
                    if (SkipInfo.skip_methods.contains(callee_name) || SkipInfo.skip_classes.contains(declaring_class)) {
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    if (declaring_class.endsWith("parsing.result.ParseResult")) {
                        if (!ie.getArg(parameter_index).getType().equals("android.content.res.XmlResourceParser")) { // Only consider the situation that pass the XmlResourceParser as the parameter.
                            Log.logData(analysis_data, "--- Pass.");
                            continue;
                        }
                    }
                    if (callee_name.startsWith("is") || callee_name.startsWith("get")) {
                        Log.logData(analysis_data, "--- Pass.");
                        continue;
                    }
                    if (!SkipInfo.no_analyzed_methods.contains(callee_name) && !SkipInfo.no_analyzed_classes.contains(declaring_class)) {
                        if (ie instanceof InterfaceInvokeExpr) { // Invoke an abstract method, try to get its body.
                            Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                            callee = Utils.getImplementedMethodOfAbstractMethod(ifi);
                            Log.logData(analysis_data,Utils.generatePartingLine("+"));
                        }
                        Value parameter = Utils.getParameter(callee, parameter_index);
                        if (parameter != null) {
                            if(!stored_methods.contains(callee)) { // This method has not been stored.
                                Log.logData(analysis_data, "--- Record the tainted method: " + callee_name);
                                stored_methods.add(callee);
                                storeMethodAndCorrespondingTaintedChildren(entry_method, new Tainted(callee, parameter, element)); // This element only related to entry method.
                                String associated_element = getAssociatedElement(entry_element, element); // This element related to entry method and its parents.
                                List<SootMethod> parents = Utils.deepCopy(entry_parents);
                                parents.add(entry_method);
                                tainted_points.offer(new Tainted(callee, parameter, associated_element, parents));
                            } else {
                                Log.logData(analysis_data, "--- This tainted method has been recoded.");
                            }
                        } else {
                            Utils.generatePartingLine("!");
                            System.out.println("Null parameter.");
                            System.out.println("method: " + callee.getSignature());
                            System.out.println("parameter index: " + parameter_index);
                            Utils.generatePartingLine("!");
                            exit(0);
                        }
                    } else {
                        Log.logData(analysis_data, "--- Pass.");
                    }
                }

                // Pass the tainted value.
                if (assignStmt == 1) {
                    AssignStmt as = (AssignStmt) unit;
                    // There is a copy of entry value.
                    if(Utils.isCopyOfValues(as, entry_value_copies)){
                        Log.logData(analysis_data, "--- Copy the entry value.");
                        Value copy = as.getLeftOp();
                        if(!entry_value_copies.contains(copy)) {
                            entry_value_copies.add(copy);
                        }
                        continue;
                    }
                    // Treat the tainted value as a whole, ignore the part (ie.e., the attribution) of it.
                    // Transfer the type of the tainted.
                    // r6 = (java.util.Set) $r10;
                    // $i2 = $r0.<android.content.pm.parsing.component.ParsedActivity: int order>;
                    List<ValueBox> vbs = as.getUseBoxes();
                    if (ie == null && vbs.size() == 2) {
                        if (!vbs.get(0).getValue().toString().startsWith("(")) {
                            Log.logData(analysis_data, "--- Pass.");
                            continue;
                        }
                    }
                    // Store some information before updating the tainted value.
                    // The tainted value is re-tainted by the entry value.
                    if (flag_entry == 1) {
                        if (tainted_value != null) {  // Have got one tainted result (by the entry value).
                            Log.logData(analysis_data, Utils.generatePartingLine("="));
                            Log.logData(analysis_data, "Store information -- re-tainted by the entry value.");
                            data_structure = tainted_value;
                            storeTaintedPointAndCorrespondingElementAndDataStructure(entry, element, data_structure); // This element only related to the entry method.
                            String associated_element = getAssociatedElement(entry_element, element); // This element related to the entry method and its parents.
                            storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure);
                            pass_tainted_value = 1;
                            if (!entry_value_copies.get(0).getType().toString().equals("android.content.res.XmlResourceParser")) {
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                                Log.logData(analysis_data, "Special entry value: this non-XmlResourceParser entry value tainted multiple places.");
                                Log.logData(analysis_data, "Entry value type: " + entry_value_copies.get(0).getType());
                                Log.logData(analysis_data, Utils.generatePartingLine("+"));
                            }
                        }
                    }
                    if (pass_tainted_value == 1) {
                        tainted_value = ((AssignStmt) unit).getLeftOp();
                        Log.logData(analysis_data, "--- Update the tainted value: " + tainted_value);
                        if (tainted_value.getType().toString().endsWith("parsing.result.ParseResult")) {
                            pass_tainted_value = 0; // Only result.getResult can be passed, when the tainted value is the type of ParseResult.
                        }
                    } else {
                        Log.logData(analysis_data, "--- Cannot update the tainted value.");
                    }
                }

                flag_skip = 0;
            }
            //System.out.println("---- block id: " + block_id);
            //System.out.println("---- flag_skip: " + flag_skip);
            if(flag_skip==1){
                skip_block_ids.add(block_id);
            }
        }

        // Store some information.
        Log.logData(analysis_data, Utils.generatePartingLine("="));
        Log.logData(analysis_data, "Store information -- analyze completely.");
        data_structure = tainted_value;
        storeTaintedPointAndCorrespondingElementAndDataStructure(entry, element, data_structure); // This element only related to the entry method.
        String associated_element = getAssociatedElement(entry_element, element); // This element related to the entry method and its parents.
        storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure);
    }

    public static void dataFlowAnalysisForMethod(Tainted entry){
        SootMethod entry_method = entry.getMethod();
        Body body = null;
        if (entry_method.isConcrete()) {
            body = entry_method.retrieveActiveBody();
        } else {
            Utils.generatePartingLine("!");
            System.out.println("This method does not have a body.");
            Utils.generatePartingLine("!");
            exit(0);
        }
        // Construct the block graph.
        CompleteBlockGraph cbg = new CompleteBlockGraph(body);

        Log.logBody(body);
        Log.logCBG(cbg);

        Utils.printPartingLine("=");
        System.out.println("+ Method: " + entry_method.getName());
        System.out.println("+ Entry value: " + entry.getValue());


        // To avoid path explosion caused by massive blocks, we start our analysis with the block we are interested in.
        // Because we ignore some blocks directly, we need save some useful information from them.
        System.out.println("Find start block...");

        Map<Value, String> valueToLikelyElement = new HashMap<Value, String>(); // The Values whose concrete value is String.
        Map<Value, String> numericValueToConcreteAssignment = new HashMap<Value, String>(); // The concrete value of all numeric Values (iX, bX, zX).

        List<Value> entry_value_copies = new ArrayList<>();
        entry_value_copies.add(entry.getValue());

        // If the method contains LookupSwitchStmts, we need to store the concrete values of numeric Values for case id transformation between two LookupSwitchStmt.
        int flag_case = 0;
        for(Unit unit : body.getUnits()){
            if(unit instanceof LookupSwitchStmt){
                flag_case = 1;
                break;
            }
        }

        Block start_block = findStartBlock(cbg, entry_value_copies, flag_case, numericValueToConcreteAssignment, valueToLikelyElement);
        if(start_block == null){ // This method no need to analysis.
            storeTaintedPointAndCorrespondingElementAndDataStructure(entry, null, null);
            Log.logData(analysis_data, "This method is not need to analyze.");
            Utils.printPartingLine("!");
            System.out.println("Cannot find the start block.");
            Utils.printPartingLine("!");
            return;
        }

        System.out.println("+ Start block id: " + start_block.getIndexInMethod());
        System.out.println("+ numeric: " + numericValueToConcreteAssignment);
        System.out.println("+ likely_element: " + valueToLikelyElement);

        // Log data.
        Log.logData(analysis_data, "+ Start block id: " + start_block.getIndexInMethod());
        Log.logData(analysis_data, "+ flag case: " + flag_case);

        // If the start block contains the method's start unit, the analysis should start with the start unit.
        Unit start_unit = entry.getStartUnit();
        int flag_start = 1;
        for(Unit unit : start_block){
            if(unit.equals(start_unit)){
                flag_start = 0;
            }
        }

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

        // Sort the paths base on the paths' length.
        // Analyze the longest path first so that we can get the most skip blocks.
        Collections.sort(Graph.paths, new ListComparator());

        Set<Unit> target_units = new HashSet<>(); // The target units of IfStmt / LookupSwitchStmt
        // If a block is analyzed, untainted, number/case/element/condition/string-insensitive, abd not the target block, it can be skipped.
        Set<Integer> skip_block_ids = new HashSet<>();
        List<SootMethod> stored_methods = new ArrayList<>();  // Avoid duplicated recoding, because multiple paths may involve the same methods.
        List<List<Integer>> analyzed_paths = new ArrayList<>(); // Avoid duplicated analysis.


        //Log data.
        Log.logData(method_data, Utils.generatePartingLine("*"));
        Log.logData(method_data, "+ Method: " + entry_method.getSignature());

        int path_num = 0;
        while(!Graph.paths.isEmpty()) {
            List<Integer> path = Graph.paths.get(0);
            //System.out.println(path.toString());
            //System.out.println(skip_block_ids.toString());
            Graph.paths.remove(0);
            List<Integer> orig_path = Utils.deepCopy(path);
            // Filter the blocks that can be skipped.
            path.removeAll(skip_block_ids);
            if(path.isEmpty()){
                path_num+=1;
                if(path_num == total_num) {
                    System.out.println("Analyzed path num: " + path_num);
                }
                continue;
            }
            if(analyzed_paths.contains(path)){
                path_num+=1;
                if(path_num == total_num) {
                    System.out.println("Analyzed path num: " + path_num);
                }
                continue;
            }
            Log.logData(analysis_data, Utils.generatePartingLine("="));
            Log.logData(analysis_data, "+ Original path: " + orig_path);
            Log.logData(analysis_data,  "+ Processed path: " + path.toString());

            dataFlowAnalysisForBlocks(cbg.getBlocks(), path, entry, entry_value_copies, flag_case, flag_start,
                    numericValueToConcreteAssignment, skip_block_ids, stored_methods, target_units, valueToLikelyElement);

            // Filter the blocks that can be skipped.
            path.removeAll(skip_block_ids);
            analyzed_paths.add(path);

            path_num+=1;
            if(path_num == total_num) {
                System.out.println("Analyzed path num: " + path_num);
            }
           /* Log.analysis_pw.close();
            Log.generatePrinterWriter(analysis_data);
            Utils.pause();*/
        }
    }
}
