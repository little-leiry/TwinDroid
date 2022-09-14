import com.sun.org.apache.xerces.internal.impl.dv.xs.AnyURIDV;
import soot.*;
import soot.jimple.*;
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

    public static final String log_file = "log_data.txt";

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
        Log.logData(log_file, Utils.generatePartingLine("-"));
        Log.logData(log_file, "associated element: " + associated_element);
        Log.logData(log_file, "data structure: " + structure);
        Log.logData(log_file, "call path: ");
        List<SootMethod> methods = Utils.deepCopy(entry_parents);
        methods.add(entry_method);
        for(SootMethod m : methods){
            Log.logData(log_file, m.getSignature());
        }
        Set<Value> ds = associatedElementToDataStructures.get(associated_element);
        if (ds == null) { // This key does not exist.
            ds = new HashSet<>();
            ds.add(data_structure);
            associatedElementToDataStructures.put(associated_element, ds);
        } else {
            ds.add(data_structure);
        }
    }

    // element: only related to the current analyzed method.
    public static void storeTaintedPointAndCorrespondingElementAndDataStructure(Tainted tainted_point, String element, Value data_structure) {
        if(element == null){
            element = "NULL";
        }
        String structure;
        if (data_structure == null){
            structure = "NULL";
        } else if (data_structure.toString().contains(".<")) {
            structure = data_structure.toString();
        } else {
            structure = data_structure.getType().toString();
        }
        Utils.printPartingLine("~");
        System.out.println("element: " + element);
        System.out.println("data structure: " + structure);
        Utils.printPartingLine("~");
        Set<Pair<String, Value>> e_ds = taintedPointToElementAndDataStructures.get(tainted_point);
        Pair<String, Value> e_d = new Pair<String, Value>(element, data_structure);
        if (e_ds == null) { // This key does not exist.
            e_ds = new HashSet<>();
            e_ds.add(e_d);
            taintedPointToElementAndDataStructures.put(tainted_point, e_ds);
        } else { // Avoid duplicate keys.
            e_ds.add(e_d);
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

    public static Map<Value, String> storeValueAndCorrespondingLikelyElement(AssignStmt as, Map<Value, String> valueToLikelyElement){
        List<ValueBox> vbs = as.getUseBoxes();
        if (vbs.size()==1 && vbs.get(0).getValue() instanceof StringConstant) {
            Value element_value = as.getLeftOp();
            String likely_element = as.getUseBoxes().get(0).getValue().toString();
            if(likely_element.startsWith("\"/")) return valueToLikelyElement;
            valueToLikelyElement.put(element_value, likely_element);
            Utils.printPartingLine("+");
            System.out.println("Likely element: " + as);
            Utils.printPartingLine("+");
        }
        return valueToLikelyElement;
    }

    public static Map<Value, String> storeNumericValueAndCorrespondingConcreteAssignment(AssignStmt as, Map<Value, String> numericValueToConcreteAssignment){
        Value def_value = as.getLeftOp();
        if(def_value.toString().contains(".<")) return numericValueToConcreteAssignment;
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
                // Replace the Value to its concrete assignment.
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
                            Utils.printPartingLine("!");
                            System.out.println("Computing Error: " + s);
                            Utils.printPartingLine("!");
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
        }
        return numericValueToConcreteAssignment;
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
                                            tainted_points.offer(new Tainted(sm, entry_value, unit));
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

    // skip_methods, skip_classes: important methods / classes. If a statement contains this kind of methods / classes, just skipping this statement.
    // no_analyzed_methods, no_analyzed_classes: these methods' / classes' functions have been known, no need to be analyzed.
    public static void dataFlowAnalysisForMethod(Tainted entry, List<String> skip_methods, List<String> no_analyzed_methods, List<String> skip_classes, List<String> no_analyzed_classes) {
        SootMethod entry_method = entry.getMethod();
        Value entry_value = entry.getValue();
        String entry_element = entry.getElement();
        Unit start_unit = entry.getStartUnit();
        int flag_start = 0;
        List<SootMethod> entry_parents = entry.getParents();

        String element = null; // For the non-switch-case situation.
        List<String> elements = null; // For the switch-case situation.
        int flag_element = 0;
        int count = 0;
        int case_num = 0;
        Value case_value = null;
        Map<Value, String> valueToLikelyElement = new HashMap<Value, String>();
        Map<String, String> caseIdToElement = new HashMap<String, String>();
        Map<Value, String> numericValueToConcreteAssignment = new HashMap<Value, String>();
        // element name => the unit associated with the element.
        Map<String, Unit> elementToUnit = new HashMap<String, Unit>();

        Value data_structure;
        Value tainted_value = null;
        int pass_tainted_value = 1;

        Body body = null;
        if (entry_method.isConcrete()) {
            body = entry_method.retrieveActiveBody();
        } else {
            Utils.printPartingLine("!");
            System.out.println("This method does not have a body.");
            Utils.printPartingLine("!");
            exit(0);
        }

        for (Unit unit : body.getUnits()) {
            if (start_unit==null){
                flag_start =1;
            }else if (start_unit.equals(unit)){
                flag_start = 1;
                continue;
            }
            if(flag_start==0) continue;

            InvokeExpr i = null;
            Value base = null;
            SootMethod callee = null;
            String callee_name = "NULL";
            String declaring_class = "NULL";
            int need_analysis = 0;
            int assignStmt = 0;
            int flag_element_cases = 0;
            int flag_entry  = 0;

            // Get the mapping relationship of elements and methods.
            // For the switch-case situation:
            // switch(element)-case(XXX)=>parseXXX(parser):
            // LookupSwitchStmt($i1){case -12356 goto z0 = equals(XXX), b2 = 0}
            // LookupSwitchStmt(b2){case 0 goto $r6 = parseXXX(parser)}
            if (unit instanceof LookupSwitchStmt) {
                LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                if (case_value != null && lss.getUseBoxes().get(0).getValue().equals(case_value)) {
                    flag_element_cases = 1;
                }
                for (int num = 0; num < lss.getTargetCount(); num++) {
                    Unit u = lss.getTarget(num);
                    InvokeExpr invoke = Utils.getInvokeOfUnit(u);
                    if (invoke != null) {
                        if (invoke.getMethod().getName().equals("equals")) { // This LookupSwitchStmt is related to elements.
                            case_num = lss.getTargetCount(); // The number of elements.
                            break;
                        }
                    }
                    if (flag_element_cases == 1) { // This LookupSwitchStmt is corresponding to the element's LookupSwitchStmt.
                        String case_id = ((Integer) lss.getLookupValue(num)).toString();
                        if (caseIdToElement.containsKey(case_id)) {
                            String e = caseIdToElement.get(case_id);
                            // Normal situation: one element associate with one unit.
                            if (!elementToUnit.containsKey(u)) {
                                elementToUnit.put(e, u);
                                Utils.printPartingLine("-");
                                System.out.println(e + " => " + u);
                            } else { // Strange situation: one element may associate with different units.
                                Unit old_unit = elementToUnit.get(e);
                                if (!old_unit.equals(u)) {
                                    Utils.printPartingLine("!");
                                    System.out.println("The associated unit of this element already exists: " + e + " => " + elementToUnit.get(e));
                                    System.out.println("Current unit is " + u);
                                    System.out.println("Method: " + entry_method.getSignature());
                                    Utils.printPartingLine("!");
                                    exit(0);
                                }
                            }
                        } else {
                            Utils.printPartingLine("!");
                            System.out.println("Cannot find the corresponding element of the case ID [ " + case_id + " ].");
                            System.out.println("Method: " + entry_method.getSignature());
                            Utils.printPartingLine("!");
                            exit(0);
                        }
                    }
                }
            }

            // Store some information before updating the elements.
            if(case_num!=0 && elementToUnit.containsValue(unit)){ // Switch-case situation.
                if(elements!=null){ // Have solved one element case.
                    data_structure = tainted_value;
                    tainted_value = null;
                    String e = elements.toString();
                    storeTaintedPointAndCorrespondingElementAndDataStructure(entry, e, data_structure); // This element only related to the entry method.
                    String associated_element = getAssociatedElement(entry_element, e);
                    storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure); // This element related to the entry method and its parents.
                }
                // Update the associated element list.
                elements = getElementsOfUnit(unit, elementToUnit);
            }

            // A statement needs to be analysed only if it contains the entry / tainted value.
            if (unit instanceof AssignStmt) {
                assignStmt = 1;
                AssignStmt as = (AssignStmt) unit;
                i = Utils.getInvokeOfAssignStmt(as);
                if (Utils.isRightValueOfAssignment(as, entry_value)){
                    flag_entry = 1;
                    need_analysis = 1;
                } else if (Utils.isRightValueOfAssignment(as, tainted_value)) {
                    need_analysis = 1;
                }
                // This entry / tainted value has been redefined.
                if (need_analysis == 0){
                    if(Utils.isLeftValueOfAssignment(as, entry_value)){
                        Utils.printPartingLine("+");
                        System.out.println("The entry value [ " + entry_value + " ] is redefined: " + as);
                        Utils.printPartingLine("+");
                        //entry_value = null;
                    } else if(Utils.isLeftValueOfAssignment(as, tainted_value)){
                        Utils.printPartingLine("+");
                        System.out.println("The tainted value [ " + tainted_value + " ] is redefined: " + as);
                        Utils.printPartingLine("+");
                        /*data_structure = tainted_value; // Store some information when the tainted value is redefined.
                        tainted_value = null;
                        String e = getElement(element, elements); // This element only related to the entry method.
                        storeTaintedPointAndCorrespondingElementAndDataStructure(entry,e,data_structure);
                        String associated_element = getAssociatedElement(entry_element, e); // This element related to the entry method and its parents.
                        storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure);*/
                    }
                }
                // This statement is likely related to an element.
                valueToLikelyElement = storeValueAndCorrespondingLikelyElement(as, valueToLikelyElement);
                // Store the byte value's concrete assignment.
                // For the case ID transform of the switch-case element.
                numericValueToConcreteAssignment = storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment);
            } else if (unit instanceof InvokeStmt) {
                i = ((InvokeStmt) unit).getInvokeExpr();
                if (Utils.isParameter(i, entry_value) != -1 || Utils.isParameter(i, tainted_value) != -1) {
                    need_analysis = 1;
                }
            }

            if (i != null) {
                callee = i.getMethod();
                callee_name = callee.getName();
                base = Utils.getBaseOfInvokeExpr(i);
            }

            // Get the element's name.
            // Store some information before updating the element.
            if (callee_name.equals("equals")) {
                if(case_num == 0 || (case_num!=0 && elementToUnit.size() == case_num)){ // Non-switch-case situation.
                    if(element!=null){ // Have solved one element case, store the result.
                        data_structure = tainted_value;
                        tainted_value = null;
                        String e = element; // This element only related to the entry method.
                        storeTaintedPointAndCorrespondingElementAndDataStructure(entry, e, data_structure);
                        String associated_element = getAssociatedElement(entry_element, e); // This element related to the entry method and its parents.
                        storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure);
                    }
                }
                if (i.getArg(0) instanceof StringConstant) { // parser.getName().equals(element)
                    element = i.getArg(0).toString();
                    flag_element = 1;
                } else if (base != null) { // element.equals(parser.getName())
                    if (valueToLikelyElement.containsKey(base)) {
                        element = valueToLikelyElement.get(base);
                        flag_element = 1;
                    }
                }
            }

            // Get the mapping relationship of two related LookupSwitchStmts' case IDs in the switch-case situation.
            if (flag_element == 1 && case_num != 0) { // The switch-case situation of multiple elements.
                count += 1;
                if (count == 3) {
                    if (assignStmt == 1) {
                        AssignStmt as = (AssignStmt) unit;
                        Value def_value = as.getLeftOp();
                        if(case_value==null){
                            if ("int_byte".contains(def_value.getType().toString())){
                                case_value = def_value;
                            } else {
                                Utils.printPartingLine("!");
                                System.out.println("Special case ID transform: " + as);
                                System.out.println("Case value type: " + def_value.getType().toString());
                                System.out.println("Method: " + entry_method.getSignature());
                                Utils.printPartingLine("!");
                                exit(0);
                            }
                        }
                        String case_id = numericValueToConcreteAssignment.get(def_value);
                        if (case_id!=null) {
                            Utils.printPartingLine("-");
                            System.out.println(case_id + " => " + element);
                            caseIdToElement.put(case_id, element);
                        } else {
                            Utils.printPartingLine("!");
                            System.out.println("Cannot find the case ID: " + as);
                            System.out.println("Method: " + entry_method.getSignature());
                            Utils.printPartingLine("!");
                            exit(0);
                        }
                    } else {
                        Utils.printPartingLine("+");
                        System.out.println("Special case (default case ID): " + unit);
                        // There is a default case ID.
                        List<String> case_ids = Utils.intToList(case_num);
                        for (String case_id : case_ids) {
                            if (!caseIdToElement.containsKey(case_id)) {
                                System.out.println(case_id + " => " + element);
                                caseIdToElement.put(case_id, element);
                            }
                        }
                        Utils.printPartingLine("+");
                    }
                    // This element case has been solved, reset the element, flag and counter.
                    element = null;
                    flag_element = 0;
                    count = 0;
                }
            }

            if (need_analysis == 0) continue;

            Utils.printPartingLine("*");
            System.out.println("Unit: " + unit);
            if(flag_entry == 1){
                System.out.println("Tainted by the entry value.");
            }
            System.out.println("Tainted value: " + tainted_value);
            //Utils.printPartingLine("*");

            // Treat the tainted / entry value as a whole, ignore the part (i.e., the attribution) of it.
            if (base != null) {
                String base_type = base.getType().toString();
                if (base.equals(tainted_value) || base.equals(entry_value)) {
                    //Utils.printPartingLine("-");
                    System.out.println("--- Tainted base.");
                    //Utils.printPartingLine("-");
                    if (base_type.endsWith("parsing.result.ParseResult")) {
                        if (!callee_name.equals("getResult")) { // ! result.getResult()
                            System.out.println("--- Pass.");
                            continue;
                        } else {
                            pass_tainted_value = 1;
                        }
                    } else {
                        if (!callee_name.startsWith("to")) { // ! tainted_value.toBundle()
                            System.out.println("--- Pass.");
                            continue;
                        }
                    }
                }
            }

            // If the tainted / entry value is passed in the callee, this callee is tainted.
            Integer parameter_index = -1;
            parameter_index = Utils.isParameter(i, entry_value);
            if(parameter_index!=-1){
                if (! entry_value.getType().toString().equals("android.content.res.XmlResourceParser")) {
                    Utils.printPartingLine("+");
                    System.out.println("Special entry value: this non-XmlResourceParser entry value tainted one method.");
                    System.out.println("Entry value: " + entry_value);
                    System.out.println("Tainted Method: " + callee.getSubSignature());
                    Utils.printPartingLine("+");
                }
            } else {
                parameter_index = Utils.isParameter(i, tainted_value);
            }
            if (parameter_index != -1) {
                //Utils.printPartingLine("-");
                System.out.println("--- Tainted callee.");
                //Utils.printPartingLine("-");
                if (callee_name.equals("add") || callee_name.equals("put")) { // xxx.add(tainted_value)
                    if (base != null) {
                        tainted_value = base;
                        System.out.println("--- Pass.");
                        continue;
                    }
                }
                if(base!=null){
                    declaring_class = ((RefType) base.getType()).getSootClass().getName();
                } else {
                    declaring_class = callee.getDeclaringClass().getName();
                }
                if (skip_methods.contains(callee_name) || skip_classes.contains(declaring_class)) {
                    System.out.println("--- Pass.");
                    continue;
                }
                if(declaring_class.endsWith("parsing.result.ParseResult")){
                    if(!i.getArg(parameter_index).getType().equals("android.content.res.XmlResourceParser")){ // Only consider the situation that pass the XmlResourceParser as the parameter.
                        System.out.println("--- Pass.");
                        continue;
                    }
                }
                if (callee_name.startsWith("is") || callee_name.startsWith("get")) {
                    System.out.println("--- Pass.");
                    continue;
                }
                if (!no_analyzed_methods.contains(callee_name) && !no_analyzed_classes.contains(declaring_class)) {
                    System.out.println("--- Record the tainted method. ");
                    if (i instanceof InterfaceInvokeExpr) { // Invoke an abstract method, try to get its body.
                        Utils.printPartingLine("+");
                        InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) i;
                        callee = Utils.getImplementedMethodOfAbstractMethod(ifi);
                        Utils.printPartingLine("+");
                    }
                    Value parameter = Utils.getParameter(callee, parameter_index);
                    if (parameter != null) {
                        String e = getElement(element, elements); // This element only related to entry method.
                        storeMethodAndCorrespondingTaintedChildren(entry_method, new Tainted(callee, parameter, e));
                        String associated_element = getAssociatedElement(entry_element, e); // This element related to entry method and its parents.
                        List<SootMethod> parents = Utils.deepCopy(entry_parents);
                        parents.add(entry_method);
                        tainted_points.offer(new Tainted(callee, parameter, associated_element, parents));
                    } else {
                        Utils.printPartingLine("!");
                        System.out.println("Null parameter.");
                        System.out.println("method: " + callee.getSignature());
                        System.out.println("parameter index: " + parameter_index);
                        Utils.printPartingLine("!");
                        exit(0);
                    }
                } else {
                    System.out.println("--- Pass.");
                }
            }

            // Pass the tainted value.
            if (assignStmt == 1 && pass_tainted_value == 1) {
                AssignStmt as = (AssignStmt) unit;
                // Treat the tainted value as a whole, ignore the part (i.e., the attribution) of it.
                //Transfer the type of the tainted / entry value.
                if (i == null && as.getUseBoxes().size() == 2) {
                    if (! as.getUseBoxes().get(0).getValue().toString().startsWith("(")) {
                        System.out.println("--- Pass.");
                        continue;
                    }
                }
                // Store some information before updating the tainted value.
                // The tainted value is re-tainted by the entry value.
                if(flag_entry==1){
                    if (tainted_value != null) {  // Have got one tainted result (by the entry value).
                        data_structure = tainted_value;
                        String e = getElement(element, elements); // This element only related to the entry method.
                        storeTaintedPointAndCorrespondingElementAndDataStructure(entry, e, data_structure);
                        String associated_element = getAssociatedElement(entry_element, e); // This element related to the entry method and its parents.
                        storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents,associated_element, data_structure);
                    }
                }
                System.out.println("--- Update the tainted value.");
                tainted_value = ((AssignStmt) unit).getLeftOp();
                if (tainted_value.getType().toString().endsWith("parsing.result.ParseResult")) {
                    pass_tainted_value = 0; // Only result.getResult can be passed, when the tainted value is the type of ParseResult.
                }
            }
        }

        // Store some information.
        data_structure = tainted_value;
        String e = getElement(element, elements); // This element only related to the entry method.
        storeTaintedPointAndCorrespondingElementAndDataStructure(entry, e, data_structure);
        String associated_element = getAssociatedElement(entry_element, e); // This element related to the entry method and its parents.
        storeAssociatedElementAndCorrespondingDataStructure(entry_method, entry_parents, associated_element, data_structure);

        if (element!=null && case_num != 0) {
            Utils.printPartingLine("+");
            System.out.println("Special situation of the element: this method contains both switch-case and non-switch-case situations.");
            System.out.println(entry_method);
            Utils.printPartingLine("+");
        }
    }
}
