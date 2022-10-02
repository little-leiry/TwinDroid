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

public class Analysis {

    // The tainted_methods needed to be analysed.
    // Each object consists of <tainted method, tainted value, associated element>
    // Use queue to do BFS.
    public static Queue<Tainted> tainted_points = new LinkedList<Tainted>();

    // element name => data structures.
    public static Map<String, Set<String>> associatedElementToDataStructures = new HashMap<String, Set<String>>();
    // method => list of <child, associated element>
    public static Map<SootMethod, Set<Analysis>> methodToTaintedChildren = new HashMap<SootMethod, Set<Analysis>>();

    // method => List of Pair<element name, data structure>
    public static Map<Analysis, Set<Pair<String, Value>>> taintedPointToElementAndDataStructures = new HashMap<Analysis, Set<Pair<String, Value>>>();

    // Judge whether the condition is met.
    // Replace the Value with its concrete assignment.
    // Sort the list according to the Value name's length first in case that one value name is the prefix of another Value name.
    public static int isConditionMet(IfStmt is, Map<Value, String> numericValueToConcreteAssignment){
        String condition = is.getCondition().toString();
        List<ValueBox> vbs = is.getUseBoxes();
        Collections.sort(vbs, new VBComparator());
        int flag_compute = 1;
        for(ValueBox vb : vbs){
            if( vb instanceof ConditionExprBox) continue;
            Value v = vb.getValue();
            if(v instanceof IntConstant) continue;
            if("int_byte_boolean".contains(vb.getValue().getType().toString())){
                String assign = numericValueToConcreteAssignment.get(v);
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
            if(Utils.hasRightValueOfAssignStmt(as, entry_value_copies)!=null) {
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
                if (Utils.hasParameterOfInvokeStmt(ie, entry_value_copies) != null) {
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
            if(Utils.hasParameterOfInvokeStmt(ie, entry_value_copies) != null) {
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

    public static int isEntryValueRedefined(AssignStmt as, List<Value> entry_values){
        return Utils.hasLeftValueOfAssignStmt(as, entry_values);
    }

    public static int isTaintedValueRedefined(AssignStmt as, InvokeExpr ie, List<Value> tainted_values, Unit tainted_unit){
        int index = Utils.hasLeftValueOfAssignStmt(as, tainted_values);
        if (index != -1) {
            if (tainted_unit != null && as.toString().equals(tainted_unit.toString())) return -1;

            if (ie != null && ie.getMethod().getDeclaringClass().toString().equals("android.content.pm.parsing.result.ParseInput"))
                return -1;

            return index;
        }
        return -1;
    }

    // Treat the tainted / entry value as a whole, ignore the part (ie., the attribution) of it.
    public static boolean canFilterForTaintedBase(String base_type, String method_name){
        if (base_type.endsWith("parsing.result.ParseResult")) {
            if (method_name.equals("getResult")) { // result.getResult()
                return false;
            }
        }
        if (base_type.equals("android.content.res.TypedArray")){
            if(!method_name.equals("peekValue")){
                return false;
            }
        }
        if (method_name.equals("get")) {
            if (base_type.endsWith("Set") || base_type.endsWith("List") || base_type.endsWith("Map")) {
                return false;
            }
        }
        if (method_name.startsWith("to") || "intern_charAt".contains(method_name)){ // Not the type transformation of the value.
            return false;
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
        if (SkipInfo.skip_methods.contains(method_name) || SkipInfo.skip_classes.contains(declaring_class)) {
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
            } else if (callee_name.startsWith("add") || callee_name.startsWith("set")){
                return true;
            } else {
                return false;
            }
        } else{
            return true;
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
                if (!SkipInfo.skip_names.contains(s) && ! s.startsWith("android.permission")) {
                    return s;
                }
            } else if (base != null && valueToLikelyElement!=null) { // element.equals(parser.getName())
                if (valueToLikelyElement.containsKey(base)) {
                    String s = valueToLikelyElement.get(base);
                    if (!SkipInfo.skip_names.contains(s) && ! s.startsWith("android.permission")) {
                        return s;
                    }
                }
            }
        }
        return null;
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
            }  else {
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

    public static String getDataStructure(Value data_structure){
        if (data_structure == null){
            return null;
        } else if (data_structure.toString().contains(".<")) {
            return data_structure.toString();
        } else {
            return data_structure.getType().toString();
        }
    }

    public static SootMethod getImplementedMethodOfAbstractMethod(InterfaceInvokeExpr ifi, Tainted tainted_point){
        Value base = ifi.getBase();
        SootMethod abstract_method = ifi.getMethod();
        SootClass abstract_cls;
        // Get the abstract class.
        if(base!=null) {
            abstract_cls = ((RefType) base.getType()).getSootClass();
        } else {
            abstract_cls = abstract_method.getDeclaringClass();
        }

        Log.logData(Log.analysis_data, "+ " + ifi);
        Log.logData(Log.analysis_data, "--- abstract class: " + abstract_cls);
        // Get the corresponding implemented classes.
        Set<SootClass> implemented_classes = Utils.abstractClassToImplementedClasses.get(abstract_cls);
        if(implemented_classes == null || implemented_classes.isEmpty()){
            Utils.printPartingLine("!");
            System.out.println("Special abstract class. Cannot find the implemented class of " + abstract_cls.getName());
            Utils.printPartingLine("!");
            return null;
        }

        SootClass implemented_cls = null;
        if(implemented_classes.size() == 1){
            implemented_cls = implemented_classes.iterator().next();
        } else {
            Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));
            Log.logData(Log.analysis_data, "Multiple implemented classes, try to confirm the concrete one ... ");
            //System.out.println(implemented_classes);
            int flag_found = 0;
            if(base!=null){
                List<Tainted> path = Utils.deepCopy(tainted_point.getParents());
                path.add(tainted_point);
                // Find the creation of the base value to confirm the implemented class.
                for (int i = path.size(); i > 0; i--) {
                    Tainted point = path.get(i-1);
                    Map<Value, Integer> parameters = point.getParameters();
                    if(parameters.get(base)!=null) { // If the base is a parameter of the method, we need analyze its parent.
                        if (i - 1 > 0) {
                            // Transform the base value.
                            Body body = path.get(i - 2).getMethod().retrieveActiveBody();
                            for (Unit unit : body.getUnits()) {
                                if (unit.equals(point.getCallUnit())) {
                                    System.out.println(point.getCallUnit());
                                    base = Utils.getInvokeOfUnit(unit).getArg(parameters.get(base));
                                    break;
                                }
                            }
                        }
                    } else { // The base is defined in this method.
                        implemented_cls = findCreationOfClassObject(point.getMethod().retrieveActiveBody(), base);
                        if (implemented_cls != null) {
                            flag_found = 1;
                            Log.logData(Log.analysis_data, "Confirmed!");
                        }
                        break;
                    }
                }
            }
            if(flag_found==0){
                implemented_cls = implemented_classes.iterator().next();
                Log.logData(Log.analysis_data, "Cannot confirm (base =  " + base + "), choose the first.");
            }
            Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));
        }

        for(SootMethod method : implemented_cls.getMethods()){
            if(method.isConcrete()){
                if(method.getSubSignature().equals(abstract_method.getSubSignature())){
                    //System.out.println("--- abstract method: " + abstract_method.getSignature());
                    Log.logData(Log.analysis_data, "--- abstract method: " + abstract_method.getSignature());
                    if(method.getDeclaration().contains(" volatile ")) { // The return types of the abstract method and its implemented method are different.
                        Body body = method.retrieveActiveBody();
                        for (Unit unit : body.getUnits()) {
                            InvokeExpr i = Utils.getInvokeOfUnit(unit);
                            if (i instanceof VirtualInvokeExpr){
                                SootMethod implemented_method = i.getMethod();
                                if(implemented_method.getName().equals(abstract_method.getName()) &&
                                        implemented_method.getParameterTypes().equals(abstract_method.getParameterTypes())) { // The actually implemented method.
                                    //System.out.println("--- implemented method: " + implemented_method.getSignature());
                                    Log.logData(Log.analysis_data, "--- implemented method: " + implemented_method.getSignature());
                                    return implemented_method;
                                }
                            }
                        }
                    }
                    //System.out.println("--- implemented method: " + method.getSignature());
                    Log.logData(Log.analysis_data, "--- implemented method: " + method.getSignature());
                    return method;
                }
            }
        }

        Utils.printPartingLine("!");
        System.out.println("Special abstract method. Cannot find the implemented method of " + abstract_method.getSignature());
        Utils.printPartingLine("!");
        return null;
    }

    // associated element: related to the current analyzed method and its parents.
    public static void storeAssociatedElementAndCorrespondingDataStructure(String associated_element, String data_structure) {
        if(associated_element==null) return;

        if (data_structure == null){
            return;
        } else if (data_structure.endsWith("parsing.result.ParseResult")){ // The parse result of this element has not been solved completely.
            return;
        }

        Set<String> ds = associatedElementToDataStructures.get(associated_element);
        if (ds == null) { // This key does not exist.
            ds = new HashSet<>();
            ds.add(data_structure);
            associatedElementToDataStructures.put(associated_element, ds);
        } else {
                ds.add(data_structure);
        }
    }

    // Store the byte value's concrete assignment.
    // For the case ID transform of the two associated switch-case statements.
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
                            Log.logData(Log.analysis_data, Utils.generatePartingLine("!"));
                            Log.logData(Log.analysis_data, "Computing Error: " + s);
                            Log.logData(Log.analysis_data, Utils.generatePartingLine("!"));
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

    public static void storeNewValueAndCorrespondingCopy(AssignStmt as, Map<Value, Value> newValueToCopy){
        if(as == null) return;

        if(Utils.isNewStmt(as)) {
            Value new_value = as.getLeftOp();
            newValueToCopy.put(new_value, null);
        } else if(Utils.hasCopyOfValues(as, new ArrayList<>(newValueToCopy.keySet()))){
            Value new_value = as.getRightOp();
            Value copy_value = as.getLeftOp();
            if(newValueToCopy.get(new_value) == null){
                newValueToCopy.put(new_value, copy_value);
            } else if (!newValueToCopy.get(new_value).equals(copy_value)) {
                Utils.printPartingLine("!");
                System.out.println("The new value [ " + new_value + " ] already has a copy : " + newValueToCopy.get(new_value));
                System.out.println("The new copy is: " + as);
                Utils.printPartingLine("!");
                exit(0);
            }

        }
    }

    public static void storeParameterOfTaintedPoint(Tainted tainted_point, IdentityStmt is){
        if(tainted_point == null || is == null) return;

        int index = Utils.isParamStmt(is);
        if(index!=-1){
            Value param = is.getLeftOp();
            tainted_point.storeParameter(param, index);
        }
    }

    public static void storeUsefulInfo(Unit unit, List<Value> entry_value_copies, int flag_case, Map<Value, Value> newValeToCopy, Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToLikelyElement){
        if(unit==null) return;

        if(unit instanceof AssignStmt) {
            AssignStmt as = (AssignStmt) unit;
            if (Utils.hasCopyOfValues(as, entry_value_copies)) {
                Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                Log.logData(Log.analysis_data, "--- Copy entry value: " + as);
                Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                Value copy = as.getLeftOp();
                if(!entry_value_copies.contains(copy)) {
                    entry_value_copies.add(copy);
                }
            }
            storeNewValueAndCorrespondingCopy(as, newValeToCopy);
            storeValueAndCorrespondingLikelyElement(as, valueToLikelyElement);
            if (flag_case == 1) {
                storeNumericValueAndCorrespondingConcreteAssignment(as, numericValueToConcreteAssignment);
            }
        }
    }

    // This statement is likely related to an element.
    public static int storeValueAndCorrespondingLikelyElement(AssignStmt as, Map<Value, String> valueToLikelyElement){
        List<ValueBox> vbs = as.getUseBoxes();
        if (vbs.size()==1 && vbs.get(0).getValue() instanceof StringConstant) {
            Value element_value = as.getLeftOp();
            String likely_element = as.getUseBoxes().get(0).getValue().toString();
            if(likely_element.startsWith("\"/")) return 1;
            valueToLikelyElement.put(element_value, likely_element);
            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
            Log.logData(Log.analysis_data, "Likely element: " + as);
            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
            return 0;
        }
        return 1;
    }

    public static void transformEntryValue(List<Value> entry_value_copies, Body body){
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
            if ("parseUsesPermission_parseUsesSdk_parseKeySets".contains(body.getMethod().getName())) { // These methods imply multiple analysis method.
                entry_value_copies.add(new_entry_value);
            } else {
                entry_value_copies.clear();
                entry_value_copies.add(new_entry_value);
            }
        }
    }

    public static void removePreviouslyTaintedValue(Value pre_tainted_value, int index, List<Value> tainted_values, Map<Value, Value> newValueToCopy){
        tainted_values.remove(pre_tainted_value);
        if (!pre_tainted_value.getUseBoxes().isEmpty()) {
            pre_tainted_value = pre_tainted_value.getUseBoxes().get(0).getValue();
        }
        Value copy = newValueToCopy.get(pre_tainted_value);
        if(copy!=null){
            tainted_values.remove(copy);
        } else if(newValueToCopy.containsValue(pre_tainted_value) && (index - 1)>0){
            Value v = tainted_values.get(index -1);
            if(newValueToCopy.containsKey(v)){
                tainted_values.remove(v);
            }
        }
    }

    public static void addNewlyTaintedValue(Value new_tainted_value, List<Value> tainted_values, Map<Value, Value> newValueToCopy){
        tainted_values.add(new_tainted_value);
        // If the tainted value is a newly constructed object, its copy is also tainted.
        if (!new_tainted_value.getUseBoxes().isEmpty()) {
            new_tainted_value = new_tainted_value.getUseBoxes().get(0).getValue();
        }
        Value copy = newValueToCopy.get(new_tainted_value);
        if(copy!=null){
            tainted_values.add(copy);
        }
    }

    public static void updateTaintedValues(Value newly_tainted_value, List<Integer> tainted_indices, List<Value> tainted_values, Map<Value, Value> newValueToCopy, String callee_name){
        // Update the tainted value.
        if(tainted_indices!=null) {
            // Remove the previously tainted value.
            for(int index : tainted_indices) {
                Value pre_tainted_value = tainted_values.get(index);
                if (pre_tainted_value.getType().toString().endsWith("parsing.result.ParseResult") && !callee_name.equals("getResult")) {
                    Log.logData(Log.analysis_data, "--- Cannot update the tainted value.");
                    return;
                }
                removePreviouslyTaintedValue(pre_tainted_value, index, tainted_values, newValueToCopy);
            }
        }
        // Add the newly tainted value.
        addNewlyTaintedValue(newly_tainted_value, tainted_values, newValueToCopy);
        Log.logData(Log.analysis_data, "--- Update the tainted value: " + tainted_values);
    }

    public static SootClass findCreationOfClassObject(Body body, Value base){
        Log.logBody(body);
        if(body == null || base == null) return null;

        for(Unit unit : body.getUnits()){
            if(unit instanceof AssignStmt){
                AssignStmt as = (AssignStmt) unit;
                if(as.getLeftOp().equals(base)){ // The definition of the base value.
                    if(Utils.isNewStmt(as)){ // The creation of the Object corresponding to the base value.
                        return ((RefType) as.getLeftOp().getType()).getSootClass();
                    } else if (as.getUseBoxes().size() == 1){ // r1 = r2;
                        base = as.getRightOp();
                        return findCreationOfClassObject(body, base);
                    } else {
                        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
                        if(ie!=null) {
                            SootMethod method = ie.getMethod();
                            if (method.isConcrete()) {
                                body = method.retrieveActiveBody();
                                base = Utils.getReturnValue(body);
                                return findCreationOfClassObject(body, base);
                            }
                        }
                        return null;
                    }
                }
            }
        }
        return  null;
    }

    public static Block findStartBlock(CompleteBlockGraph cbg, Tainted entry, List<Value> entry_value_copies, int flag_case, Map<Value, Value> newValueToCopy,
                                       Map<Value, String> numericValueToConcreteAssignment, Map<Value, String> valueToLikelyElement){
        if(cbg==null || entry_value_copies == null) return null;

        Block start_block = null;

        for(Block block : cbg.getBlocks()){
            for(Unit unit : block){
                if(isInterestedUnit(unit, entry_value_copies, valueToLikelyElement)){
                    System.out.println("Interested unit: " + unit);
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
                            start_block = block;
                            break;
                        }
                    }
                    if(start_block!=null) break;
                }
                // Store some information before we skip the unit.
                storeUsefulInfo(unit, entry_value_copies, flag_case, newValueToCopy, numericValueToConcreteAssignment, valueToLikelyElement);
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
                                            List<Value> entry_values = new ArrayList<>();
                                            entry_values.add(as.getLeftOp());
                                            tainted_points.offer(new Tainted(sm, entry_values, unit, body.getUnits().getSuccOf(unit)));
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
                                                 Map<Value, Value> newValueToCopy, Map<Value, String> numericValueToConcreteAssignment,
                                                 List<SootMethod> recorded_methods, Map<Value, String> valueToLikelyElement) {

        SootMethod entry_method = entry.getMethod();
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

        for (int i = 0; i< block_ids.size(); i++) {
            int block_id = block_ids.get(i);
            Block block = blocks.get(block_id);
            for (Unit unit : block) {
                // Store useful information from this unit.
                storeUsefulInfo(unit, entry_values_path, flag_case, newValueToCopy, numericValueToConcreteAssignment_path, valueToLikelyElement_path);
                // Analysis should start with the start unit.
                if(flag_start == 0){
                    if (start_unit.equals(unit)) {
                        flag_start = 1;
                    }
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
                List<Integer> entry_indices = null; // The entry values' indices that this unit contains.
                List<Integer> tainted_indices = null; // The tainted values' indices that this unit contains.


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
                        LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                        if (case_value == null) { // Get the bridge case value between two LookupSwitchStmts.
                            case_value = getCaseValue(lss);
                        }
                        // Filter wrong paths.
                        if (case_value != null && lss.getKey().equals(case_value)) {
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
                                        Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                                        Log.logData(Log.analysis_data, "Case value: " + case_value + " => " + case_id);
                                        Log.logData(Log.analysis_data, "Target unit (hash code): " + target_unit.hashCode());
                                        Log.logData(Log.analysis_data, "Next block head (hash code): " + next_block_head.hashCode());
                                        Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                                        // If the next block's first Unit is not the target Unit, this path is incorrect.
                                        if (!next_block_head.equals(target_unit)) {
                                            Utils.generatePartingLine("!");
                                            Log.logData(Log.analysis_data, "Wrong path, stop analyzing!");
                                            Utils.generatePartingLine("!");
                                            return;
                                        }
                                    } else {
                                        Log.logData(Log.analysis_data, Utils.generatePartingLine("!"));
                                        Log.logData(Log.analysis_data, "Special path, the end block contains LookupSwitchStmt.");
                                        Log.logData(Log.analysis_data, block_ids.toString());
                                        Log.logData(Log.analysis_data, Utils.generatePartingLine("!"));
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
                    IfStmt is = (IfStmt) unit;
                    int result = isConditionMet(is, numericValueToConcreteAssignment_path);
                    if(result != -1 ){
                        Unit target_unit = is.getTarget();
                        if(target_unit==null){
                            Utils.generatePartingLine("!");
                            System.out.println("Cannot find the target Unit of the IfStmt: " + is);
                            System.out.println("Method: " + entry_method.getSignature());
                            Utils.generatePartingLine("!");
                            exit(0);
                        }
                        if(i + 1 <block_ids.size()) {
                            if (result == 1) {
                                // When the condition is met, if the next block's first Unit is not the target Unit, this path is incorrect.
                                if (!blocks.get(block_ids.get(i + 1)).getHead().equals(target_unit)) {
                                    Utils.generatePartingLine("!");
                                    Log.logData(Log.analysis_data, "--- Wrong path, stop analyzing!");
                                    Utils.generatePartingLine("!");
                                    return;
                                }
                            } else {
                                // When the condition is not met, if the next block's first Unit is the target Unit, this path is incorrect.
                                if (blocks.get(block_ids.get(i + 1)).getHead().equals(target_unit)) {
                                    Utils.generatePartingLine("!");
                                    Log.logData(Log.analysis_data, "Wrong path, stop analyzing!");
                                    Utils.generatePartingLine("!");
                                    return;
                                }
                            }
                        } else {
                            Log.logData(Log.analysis_data, Utils.generatePartingLine("!"));
                            Log.logData(Log.analysis_data, "Special path, the end block contains IfStmt.");
                            Log.logData(Log.analysis_data, block_ids.toString());
                            Log.logData(Log.analysis_data, Utils.generatePartingLine("!"));
                        }
                    }
                    continue;
                }

                // A statement needs to be analysed only if it contains the entry / tainted value.
                if (unit instanceof AssignStmt) {
                    assignStmt = 1;
                    AssignStmt as = (AssignStmt) unit;
                    ie = Utils.getInvokeOfAssignStmt(as);
                    entry_indices = Utils.hasRightValueOfAssignStmt(as, entry_value_copies);
                    tainted_indices = Utils.hasRightValueOfAssignStmt(as, tainted_values);
                    if(entry_indices != null || tainted_indices != null){
                        need_analysis = 1;
                    }
                    // This entry / tainted value has been re-defined.
                    if (need_analysis == 0) {
                        int index = isEntryValueRedefined(as, entry_values_path);
                        if (index != -1) {
                            entry_values_path.remove(index);
                            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                            Log.logData(Log.analysis_data, "+ Unit: " + as);
                            Log.logData(Log.analysis_data, "--- The entry value [ " + as.getLeftOp() + " ] is re-defined, remove it.");
                            Log.logData(Log.analysis_data, "--- Updated the entry value: " + entry_values_path);
                            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                        } else {
                            index = isTaintedValueRedefined(as, ie, tainted_values, tainted_unit);
                            if (index != -1) {
                                Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                                Log.logData(Log.analysis_data, "+ Unit: " + as);
                                Log.logData(Log.analysis_data, "--- The tainted value [ " + as.getLeftOp() + " ] is re-defined.");
                                Value pre_tainted_value = tainted_values.get(index);
                                data_structure = getDataStructure(pre_tainted_value); // Store some information when the tainted value is redefined.
                                Log.logData(Log.analysis_data, "Store the information -- value re-defined.");
                                entry.storeInnerElementAndStructure(element, data_structure); // This element only related to the entry method.
                                String associated_element = getAssociatedElement(entry_element, element); // This element related to the entry method and its parents.
                                storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
                                removePreviouslyTaintedValue(pre_tainted_value, index, tainted_values, newValueToCopy);
                                tainted_unit = null;
                                Log.logData(Log.analysis_data, "--- Update the tainted value: " + tainted_values);
                                Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                            }
                        }
                    }
                } else if (unit instanceof InvokeStmt) {
                    ie = ((InvokeStmt) unit).getInvokeExpr();
                    entry_indices = Utils.hasParameterOfInvokeStmt(ie, entry_values_path);
                    tainted_indices = Utils.hasParameterOfInvokeStmt(ie, tainted_values);
                    if(entry_indices!=null || tainted_indices!= null) {
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
                    String old_element = element;
                    if(old_element != null) { // Have solved one element case.
                        // Store some information before updating the element.
                        Log.logData(Log.analysis_data, Utils.generatePartingLine("="));
                        Log.logData(Log.analysis_data, "Store information -- element update.");
                        if(tainted_values.isEmpty()){
                            tainted_values.add(null);
                        }
                        for(Value v : tainted_values){
                            data_structure = getDataStructure(v);
                            entry.storeInnerElementAndStructure(old_element, data_structure); // This element only related to the entry method.
                            String associated_element = getAssociatedElement(entry_element, old_element); // This element related to the entry method and its parents.
                            storeAssociatedElementAndCorrespondingDataStructure(associated_element, data_structure);
                        }
                        tainted_values.clear();
                        tainted_unit = null;
                    }
                    // Update the element.
                    element = s;
                    Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                    Log.logData(Log.analysis_data, "Element: " + element);
                    Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                    continue;
                }

                if (need_analysis == 0){
                    continue;
                }

                Log.logData(Log.analysis_data, Utils.generatePartingLine("="));
                Log.logData(Log.analysis_data, "+ Unit: " + unit);
                if (entry_indices!=null) {
                    Log.logData(Log.analysis_data, "--- Tainted by the entry value.");
                }
                if(tainted_indices!=null){
                    Log.logData(Log.analysis_data, "--- Tainted value: " + tainted_values);
                }

                // Treat the tainted / entry value as a whole, ignore the part (ie., the attribution) of it.
                if (base != null) {
                    String base_type = base.getType().toString();
                    if (tainted_values.contains(base) || entry_values_path.contains(base)) {
                        Log.logData(Log.analysis_data, "--- Tainted base.");
                        if(canFilterForTaintedBase(base_type, callee_name)){
                            Log.logData(Log.analysis_data, "--- Pass.");
                            continue;
                        }
                    }
                }

                // If the tainted / entry value is passed in the callee, this callee is tainted.
                Set<Integer> param_indices = new HashSet<>();
                if(entry_indices!=null){
                    for(int index : entry_indices){
                        Integer param_index = Utils.isParameterOfInvokeStmt(ie,entry_values_path.get(index));
                        if(param_index!=-1){
                            param_indices.add(param_index);
                        }
                    }
                }
                if(tainted_indices!=null){
                    for(int index : tainted_indices){
                        Integer param_index = Utils.isParameterOfInvokeStmt(ie, tainted_values.get(index));
                        if(param_index!=-1){
                            param_indices.add(param_index);
                        }
                    }
                }
                if(!param_indices.isEmpty()){
                    Log.logData(Log.analysis_data, "--- Tainted callee.");
                    int flag_array = 0;
                    int flag_parser = 0;
                    for(int param_index : param_indices){
                        String param_type = ie.getArg(param_index).getType().toString();
                        if(param_type.equals("android.content.res.TypedArray")){
                            flag_array = 1;
                        } else if(param_type.equals("android.content.res.XmlResourceParser")){
                            flag_parser = 1;
                        }
                    }
                    if(canFilterForTaintedParameter(base, callee, callee_name, flag_array)){
                        Log.logData(Log.analysis_data, "--- Pass.");
                        continue;
                    }
                    if(callee.isConstructor()){
                        if(base != null){
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            tainted_unit = unit;
                            updateTaintedValues(newly_tainted_value, tainted_indices, tainted_values, newValueToCopy, callee_name);
                            continue;
                        }
                    }
                    if (callee_name.equals("add") || callee_name.equals("put")) { // xxx.add(tainted_value)
                        if (base != null) {
                            // Update the tainted value.
                            Value newly_tainted_value = base;
                            tainted_unit = unit;
                            updateTaintedValues(newly_tainted_value, tainted_indices, tainted_values, newValueToCopy, callee_name);
                            continue;
                        }
                    }
                    if(callee_name.equals("arraycopy")){
                        // Update the tainted value.
                        Value newly_tainted_value = ie.getArg(2);
                        tainted_unit = unit;
                        updateTaintedValues(newly_tainted_value, tainted_indices, tainted_values, newValueToCopy, callee_name);
                        continue;
                    }
                    if(needRecordMethod(assignStmt, flag_parser, callee_name)){
                        if (ie instanceof InterfaceInvokeExpr) { // Invoke an abstract method, try to get its body.
                            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
                            InterfaceInvokeExpr ifi = (InterfaceInvokeExpr) ie;
                            callee = getImplementedMethodOfAbstractMethod(ifi, entry);
                            Log.logData(Log.analysis_data,Utils.generatePartingLine("+"));
                        }
                        List<Value> parameters = new ArrayList<>();
                        for(int param_index : param_indices) {
                            Value parameter = Utils.getParameterOfMethod(callee, param_index);
                            if(parameter!=null){
                                parameters.add(parameter);
                            } else {
                                Utils.printPartingLine("!");
                                System.out.println("Null parameter.");
                                System.out.println("method: " + callee.getSignature());
                                System.out.println("parameter index: " + param_index);
                                Utils.printPartingLine("!");
                                exit(0);
                            }
                        }
                        if(!recorded_methods.contains(callee)) { // This method has not been stored.
                            Log.logData(Log.analysis_data, "--- Record the tainted method: " + callee_name);
                            recorded_methods.add(callee);
                            entry.storeTaintedChildren(new Tainted(callee, parameters, element, unit)); // This element only related to entry method.
                            String associated_element = getAssociatedElement(entry_element, element); // This element related to entry method and its parents.
                            List<Tainted> parents = Utils.deepCopy(entry_parents);
                            parents.add(entry);
                            tainted_points.offer(new Tainted(callee, parameters, associated_element, parents, unit));
                        } else {
                            Log.logData(Log.analysis_data, "--- This tainted method has been recoded.");
                        }
                    }
                }

                // Pass the tainted value.
                if (assignStmt == 1) {
                    AssignStmt as = (AssignStmt) unit;
                    // There is a copy of entry value.
                    if(Utils.hasCopyOfValues(as, entry_values_path)){
                        continue;
                    }
                    // Treat the tainted / entry value as a whole, ignore the part (ie.e., the attribution) of it.
                    // Transfer the type of the tainted -- r6 = (java.util.Set) $r10;
                    // Assign the value to a filed --
                    // r0.<android.content.pm.parsing.ParsingPackageImpl: java.util.List permissions> = $r2;
                    if (ie == null && as.getUseBoxes().size() == 2) {
                        if(! as.getLeftOp().toString().contains(".<") && !as.getRightOp().toString().startsWith("(")){
                            Log.logData(Log.analysis_data, "--- Pass.");
                            continue;
                        }
                    }
                    // Update the tainted value.
                    Value newly_tainted_value = as.getLeftOp();
                    tainted_unit = unit;
                    updateTaintedValues(newly_tainted_value, tainted_indices, tainted_values, newValueToCopy,callee_name);
                }
            }
        }

        // Store some information.
        Log.logData(Log.analysis_data, Utils.generatePartingLine("="));
        Log.logData(Log.analysis_data, "Store information -- analyze completely.");
        if(tainted_values.isEmpty()){
            tainted_values.add(null);
        }
        for(Value v : tainted_values) {
            data_structure = getDataStructure(v);
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

        // If the method contains LookupSwitchStmts, we need to store the concrete values of numeric Values for case id transformation between two LookupSwitchStmt.
        int flag_case = 0;
        for(Unit unit : body.getUnits()){
            if(unit instanceof IdentityStmt){
                IdentityStmt is = (IdentityStmt) unit;
                storeParameterOfTaintedPoint(entry, is);
            } else if (unit instanceof LookupSwitchStmt){
                flag_case = 1;
                break;
            }
        }
        // To avoid path explosion caused by massive blocks, we start our analysis with the block we are interested in.
        // Because we ignore some blocks directly, we need save some useful information from them.
        System.out.println("Find start block...");
        // The general analysis method -- treats the element parser as a whole and gets its parse result.
        // The secondary analysis method -- gets the attributions of the element parser.
        // The parseUsesPermission / parseUsesSdk / parseKeySets implements multiple analysis methods.
        if("parseUsesPermission_parseUsesSdk_parseKeySets". contains(body.getMethod().getName())){
            transformEntryValue(entry_value_copies, body);
            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
            Log.logData(Log.analysis_data, "Transform the entry value :" + entry_value_copies);
            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
        }
        Block start_block = findStartBlock(cbg, entry, entry_value_copies, flag_case, newValueToCopy, numericValueToConcreteAssignment, valueToLikelyElement);
        if(start_block == null){
            // These methods do not implement the general analysis methods.
            // We need transform the entry value.
            System.out.println("Transform the entry value...");
            transformEntryValue(entry_value_copies, body);
            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
            Log.logData(Log.analysis_data, "Transform the entry value :" + entry_value_copies);
            Log.logData(Log.analysis_data, Utils.generatePartingLine("+"));
            // Find the start block again.
            start_block = findStartBlock(cbg, entry, entry_value_copies, flag_case, newValueToCopy, numericValueToConcreteAssignment, valueToLikelyElement);
            if(start_block == null) { // This method no needs to analysis.
                entry.storeInnerElementAndStructure(null, null);
                entry.storeTaintedChildren(null);
                Log.logData(Log.analysis_data, "This method does not need to be analyzed.");
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
        Log.logData(Log.analysis_data, "+ Start block id: " + start_block.getIndexInMethod());
        Log.logData(Log.analysis_data, "+ flag case: " + flag_case);

        // If the start block contains the method's start unit, the analysis should start with the start unit.
        Unit start_unit = entry.getStartUnit();
        int flag_start = 1;
        for(Unit unit : start_block){
            if(unit.equals(start_unit)){
                flag_start = 0;
                break;
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
        if(total_num > 50000){
            System.out.println("To many paths.");
            Log.logData(Log.analysis_data, "Path number > 50000, change.");
            Graph.paths.clear();
            List<Integer> path = new ArrayList<>();
            for (int i = start_block.getIndexInMethod(); i < cbg.getBlocks().size(); i++) {
                path.add(i);
            }
            Graph.paths.add(path);
        }

        //Log data.
        Log.logData(Log.method_data, Utils.generatePartingLine("*"));
        Log.logData(Log.method_data, "+ Method: " + entry_method.getSignature());

        int path_num = 0;
        List<SootMethod> stored_methods = new ArrayList<>();  // Avoid duplicated recoding, because multiple paths may involve the same methods.
        while(!Graph.paths.isEmpty()) {
            List<Integer> path = Graph.paths.get(0);
            Graph.paths.remove(0);
            Log.logData(Log.analysis_data, Utils.generatePartingLine("*"));
            Log.logData(Log.analysis_data, "+ Path: " + path);
            dataFlowAnalysisForBlocks(cbg.getBlocks(), path, entry, entry_value_copies, flag_case, flag_start, newValueToCopy,
                    numericValueToConcreteAssignment, stored_methods, valueToLikelyElement);
            path_num+=1;
            if(path_num == total_num || path_num % 1000 == 0) {
                System.out.println("Analyzed path num: " + path_num);
            }
           /* Log.analysis_pw.close();
            Log.generatePrinterWriter(analysis_data);
            Utils.pause();*/
        }
    }
}
