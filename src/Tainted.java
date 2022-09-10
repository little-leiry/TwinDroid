import soot.*;
import soot.jimple.*;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class Tainted {
    private SootMethod mMethod;
    private Value mValue;
    private String mElement;
    private List<SootMethod> mParents;
    // The tainted_methods needed to be analysed. Soot
    // Each object consists of <tainted method, tainted value, associated element>
    // Use queue to do BFS.
    public static Queue<Tainted> tainted_methods = new LinkedList<Tainted>();

    // element name => data structures.
    public static Map<String, Set<Value>> elementToDataStructures = new HashMap<String, Set<Value>>();

    // method => List of Pair<element name, data structure>
    public static Map<SootMethod, Set<Pair<String, Value>>> methodToElementAndDataStructures = new HashMap<SootMethod, Set<Pair<String, Value>>>();

    public static final String log_file = "log_data.txt";

    public Tainted(SootMethod method, Value value, String element, List<SootMethod> parents) {
        mMethod = method;
        mValue = value;
        mElement = element;
        mParents = parents;
    }

    public SootMethod getMethod(){
        return mMethod;
    }

    public Value getValue(){
        return mValue;
    }

    public String getAssociatedElement(){
        return mElement;
    }

    public List<SootMethod> getParents(){
        return mParents;
    }

    public static String getAssociatedElement(String entry_element, String element, List<String> associated_elements){
        if(!element.equals("NULL")){
            if(!entry_element.equals("NULL")){
                return entry_element+"_"+element;
            } else {
                return element;
            }
        } else if(associated_elements.size()>0){
                if(!entry_element.equals("NULL")){
                    return entry_element + "_" + associated_elements.toString();
                } else {
                    return associated_elements.toString();
                }
        } else {
            return entry_element;
        }
    }

    public static List<String> getElementsOfUnit(Unit unit, Map<String, Unit> elementToUnit) {
        List<String> elements = new ArrayList<>(); //One method may correspond to multiple elements.
        if (elementToUnit.containsValue(unit)) {
            for (Map.Entry<String, Unit> entry : elementToUnit.entrySet()) {
                if (unit.equals(entry.getValue())) {
                    elements.add(entry.getKey());

                }
            }
        }
        return elements;
    }

    public static void storeElementAndCorrespondingDataStructure(String element, Value data_structure) {
        Log.logData(log_file, "element: " + element);
        if(data_structure.toString().contains(".<")) {
            Log.logData(log_file, "data structure: " + data_structure.toString());
        } else {
            Log.logData(log_file, "data structure: " + data_structure.getType().toString());
        }
        Set<Value> ds = elementToDataStructures.get(element);
        if (ds == null) { // This key does not exist.
            ds = new HashSet<>();
            ds.add(data_structure);
            elementToDataStructures.put(element, ds);
        } else {
            ds.add(data_structure);
        }
    }

    public static void storeMethodAndCorrespondingElementAndDataStructure(SootMethod method, String element, Value data_structure) {
        Set<Pair<String, Value>> e_ds = methodToElementAndDataStructures.get(method);
        Pair<String, Value> e_d = new Pair<String, Value>(element, data_structure);
        if (e_ds == null) { // This key does not exist.
            e_ds = new HashSet<>();
            e_ds.add(e_d);
            methodToElementAndDataStructures.put(method, e_ds);
        } else { // Avoid duplicate keys.
            e_ds.add(e_d);
        }
    }

    public static void findEntryPoints() {
        //Map<SootMethod, Value> entries = new HashMap<SootMethod,Value>();
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
                                            System.out.println(as);
                                            Value entry = as.getLeftOp();
                                            tainted_methods.offer(new Tainted(sm, entry, "NULL", new ArrayList<>()));
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
        String entry_element = entry.getAssociatedElement();
        List<SootMethod> entry_parents = entry.getParents();
        Log.logData(log_file, Utils.generatePartingLine("#"));
        Log.logData(log_file, "analyze method: " + entry_method);
        Log.logData(log_file, "call path: " + entry_parents.toString());
        String element = "NULL";
        List<String> associated_elements = new ArrayList<>(); // For the switch-case situation.
        int flag_element = 0;
        int count = 0;
        int case_num = 0;
        Value case_value = null;
        Map<Value, String> valueToLikelyElement = new HashMap<Value, String>();
        Map<String, String> caseIdToElement = new HashMap<String, String>();
        // element name => the unit associated with the element.
        Map<String, Unit> elementToUnit = new HashMap<String, Unit>();
        Value data_structure = null;
        Value tainted_value = null;
        int pass_tainted_value = 1;
        Body body = null;
        if (entry_method.isConcrete()) {
            body = entry_method.retrieveActiveBody();
        } else {
            Utils.generatePartingLine("!");
            System.out.println("The method " + entry_method.getSignature() + " does not have a body.");
            Utils.generatePartingLine("!");
            return;
        }
        for (Unit unit : body.getUnits()) {
            InvokeExpr i = null;
            Value base = null;
            SootMethod callee = null;
            String callee_name = "NULL";
            String declaring_class = "NULL";
            int need_analysis = 0;
            int assignStmt = 0;
            int flag_element_cases = 0;

            if(case_num!=0 && elementToUnit.containsValue(unit)){ // Switch-case situation.
                if(associated_elements!=null && tainted_value!=null &&
                        !tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")) { // Have solved one element case.
                    data_structure = tainted_value;
                    tainted_value = null;
                    for (String e : associated_elements) {
                        if(!entry_element.equals("NULL")){
                            e = entry_element+"_"+e;
                        }
                        storeElementAndCorrespondingDataStructure(e, data_structure);
                        storeMethodAndCorrespondingElementAndDataStructure(entry_method, e, data_structure);
                    }
                }
                // Update the associated element list.
                associated_elements = getElementsOfUnit(unit, elementToUnit);
            }
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
                                Utils.generatePartingLine("-");
                                System.out.println(e + " => " + u);
                            } else { // Strange situation: one element may associate with different units.
                                Unit old_unit = elementToUnit.get(e);
                                if (!old_unit.equals(u)) {
                                    Utils.generatePartingLine("!");
                                    System.out.println("The associated unit of this element already exists: " + e + " => " + elementToUnit.get(e));
                                    System.out.println("Current unit is " + u);
                                    Utils.generatePartingLine("!");
                                }
                            }
                            if (invoke == null) {
                                System.out.println("!!! Special element cases. The target unit does not contain an InvokeExpr.");
                            }
                        }
                    }
                }
            }

            // A statement needs to be analysed only if it contains the entry / tainted value.
            if (unit instanceof AssignStmt) {
                assignStmt = 1;
                AssignStmt as = (AssignStmt) unit;
                i = Utils.getInvokeOfAssignStmt(as);
                if (Utils.isUsedValueOfAssignment(as, entry_value) || Utils.isUsedValueOfAssignment(as, tainted_value)) {
                    need_analysis = 1;
                }
                // This entry / tainted value has been redefined.
                if (!Utils.isUsedValueOfAssignment(as, entry_value) && !Utils.isUsedValueOfAssignment(as, tainted_value)){
                    if(Utils.isDefValueOfAssignment(as, entry_value)){
                        entry_value = null;
                    } else if(Utils.isDefValueOfAssignment(as, tainted_value)){
                        data_structure = tainted_value; // Store the tainted value as the data structure if it is redefined.
                        tainted_value = null;
                        String e = getAssociatedElement(entry_element, element, associated_elements);
                        storeElementAndCorrespondingDataStructure(e, data_structure);
                        storeMethodAndCorrespondingElementAndDataStructure(entry_method,e,data_structure);
                    }
                }
                if (as.getUseBoxes().get(0).getValue() instanceof StringConstant) { // This statement is likely related to an element.
                    Value element_value = as.getLeftOp();
                    String likely_element = as.getUseBoxes().get(0).getValue().toString();
                    valueToLikelyElement.put(element_value, likely_element);
                    Utils.generatePartingLine("+");
                    System.out.println("Likely element: " + as);
                    Utils.generatePartingLine("+");
                }
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
            if (callee_name.equals("equals")) {
                if(case_num == 0 || (case_num!=0 && elementToUnit.size() == case_num)){ // Non-switch-case situation.
                    if(!element.equals("NULL") && tainted_value != null &&
                            !tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")){ // Have solved one element case, store the result.
                        data_structure = tainted_value;
                        tainted_value = null;
                        String e = element;
                        if(!entry_element.equals("NULL")){
                            e= entry_element + "_" + e;
                        }
                        storeElementAndCorrespondingDataStructure(e, data_structure);
                        storeMethodAndCorrespondingElementAndDataStructure(entry_method, e, data_structure);
                    }
                }
                if (i.getArg(0) instanceof StringConstant) { // parser.getName().equals(element)
                    element = i.getArg(0).toString();
                } else if (base != null) { // element.equals(parser.getName())
                    if (valueToLikelyElement.containsKey(base)) {
                        element = valueToLikelyElement.get(base);
                    }
                }
                flag_element = 1;
            }

            if (flag_element == 1 && case_num != 0) { // The switch-case situation of multiple elements.
                count += 1;
                // Get the mapping relationship of two related LookupSwitchStmts' case IDs
                if (count == 3) {
                    if (assignStmt == 1) {
                        AssignStmt as = (AssignStmt) unit;
                        String case_id = as.getUseBoxes().get(0).getValue().toString();
                        if (Utils.isNumeric(case_id)) {
                            if (case_value == null) {
                                case_value = as.getLeftOp();
                            }
                            Utils.generatePartingLine("-");
                            System.out.println(case_id + " => " + element);
                            caseIdToElement.put(case_id, element);
                        } else {
                            Utils.generatePartingLine("!");
                            System.out.println("Special case id: " + unit);
                            Utils.generatePartingLine("!");
                        }
                    } else {
                        Utils.generatePartingLine("!");
                        System.out.println("Special case: " + unit);
                        Utils.generatePartingLine("!");
                        // There is a default case ID.
                        List<String> case_ids = Utils.intToList(case_num);
                        for (String case_id : case_ids) {
                            if (!caseIdToElement.containsKey(case_id)) {
                                System.out.println(case_id + " => " + element);
                                caseIdToElement.put(case_id, element);
                            }
                        }
                    }
                    // This element case has been solved, reset the element's initial value, flag and counter.
                    element = "NULL";
                    flag_element = 0;
                    count = 0;
                }
            }

            if (need_analysis == 0) continue;
            Utils.generatePartingLine("*");
            System.out.println("unit: " + unit);
            System.out.println("entry value: " + entry_value);
            if (tainted_value != null) {
                System.out.println("tainted value: " + tainted_value);
            }
            Utils.generatePartingLine("*");

            // Treat the tainted / entry value as a whole, ignore the part (i.e., the attribution) of it.
            if (base != null) {
                String base_type = base.getType().toString();
                if (base.equals(tainted_value) || base.equals(entry_value)) {
                    Utils.generatePartingLine("-");
                    System.out.println("tainted base: " + unit);
                    Utils.generatePartingLine("-");
                    if (base_type.equals("android.content.pm.parsing.result.ParseResult")) {
                        if (!callee_name.equals("getResult")) { // ! result.getResult()
                            continue;
                        } else {
                            pass_tainted_value = 1;
                        }
                    } else {
                        if (!callee_name.startsWith("to")) continue; // ! tainted_value.toBundle()
                    }
                }
            }

            // If the tainted / entry value is passed in the callee, this callee is tainted.
            Integer parameter_index = -1;
            int flag_entry = 0;
            parameter_index = Utils.isParameter(i, entry_value);
            if(parameter_index!=-1){
                flag_entry = 1;
            } else {
                parameter_index = Utils.isParameter(i, tainted_value);
            }
            if (parameter_index != -1) {
                Utils.generatePartingLine("-");
                System.out.println("tainted callee: " + unit);
                Utils.generatePartingLine("-");
                if (callee_name.equals("add") || callee_name.equals("put")) { // xxx.add(tainted_value)
                    if (base != null) {
                        tainted_value = base;
                        continue;
                    }
                }
                if(base!=null){
                    declaring_class = ((RefType) base.getType()).getSootClass().getName();
                } else {
                    declaring_class = callee.getDeclaringClass().getName();
                }
                if (skip_methods.contains(callee_name) || skip_classes.contains(declaring_class)) continue;
                if (callee_name.startsWith("is")) continue;
                if (!no_analyzed_methods.contains(callee_name) && !no_analyzed_classes.contains(declaring_class)) {
                    if (i instanceof InterfaceInvokeExpr) { // Invoke an abstract method.
                        Utils.generatePartingLine("-");
                        InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) i;
                        callee = Utils.getImplementedMethodOfAbstractMethod(ifi);
                        Utils.generatePartingLine("-");
                    }
                    Value parameter = Utils.getParameter(callee, parameter_index);
                    if (parameter != null) {
                        String e = getAssociatedElement(entry_element, element, associated_elements);
                        List<SootMethod> parents = Utils.deepCopy(entry_parents);
                        parents.add(entry_method);
                        tainted_methods.offer(new Tainted(callee, parameter, e, parents));
                    } else {
                        Utils.generatePartingLine("!");
                        System.out.println("Null parameter.");
                        System.out.println("method: " + callee.getSignature());
                        System.out.println("parameter index: " + parameter_index);
                        Utils.generatePartingLine("!");
                    }
                }
            }

            if(flag_entry==1){
                if (tainted_value != null && !tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")) {  // Have got one tainted result (by the entry value).
                    data_structure = tainted_value;
                    tainted_value = null;
                    String e = getAssociatedElement(entry_element, element, associated_elements);
                    storeElementAndCorrespondingDataStructure(e, data_structure);
                    storeMethodAndCorrespondingElementAndDataStructure(entry_method, e, data_structure);
                }
                if (! entry_value.getType().toString().equals("android.content.res.XmlResourceParser")) {
                    Utils.generatePartingLine("!");
                    System.out.println("Special entry value: this non-XmlResourceParser entry value tainted multiple methods.");
                    System.out.println("method: " + callee.getSubSignature());
                    System.out.println("entry value: " + entry_value);
                    Utils.generatePartingLine("!");
                }
            }

            // Pass the tainted value.
            if (assignStmt == 1 && pass_tainted_value == 1) {
                AssignStmt as = (AssignStmt) unit;
                // r6 = (java.util.Set) $r10 => Transfer the type of the tainted value
                // $r7 = r11.<android.content.pm.parsing.component.ParsedProcess: java.lang.String name> => Obtain the attribution of the tainted value
                if (i == null && as.getUseBoxes().size() == 2) {
                    if (as.getUseBoxes().get(0).toString().contains(".<"))
                        continue; // Treat the tainted value as a whole, ignore the part (i.e., the attribution) of it.
                }
                tainted_value = ((AssignStmt) unit).getLeftOp();
                if (tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")) {
                    pass_tainted_value = 0; // Only result.getResult can be passed, when the tainted value is the type of ParseResult.
                }
            }
        }

        if (!element.equals("NULL") && case_num != 0) {
            Utils.generatePartingLine("!");
            System.out.println("Special situation of the element: this method contains both switch-case and non-switch-case situations.");
            System.out.println(entry_method);
            Utils.generatePartingLine("!");
        }

        if (tainted_value != null && !tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")) {
            data_structure = tainted_value;
            String e = getAssociatedElement(entry_element, element, associated_elements);
            storeElementAndCorrespondingDataStructure(e, data_structure);
            storeMethodAndCorrespondingElementAndDataStructure(entry_method, e, data_structure);
        }
    }
}
