import org.w3c.dom.ls.LSOutput;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.ConditionExprBox;
import soot.toolkits.graph.Block;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.util.*;

import static java.lang.System.exit;

public class Analysis {
    public Analysis(){}

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

    public static boolean isWrongPathForIfStmt(List<Block> blocks, List<Integer> block_ids, int block_ids_index, IfStmt is, Map<Value, String> numericValueToConcreteAssignment) {
        int result = isConditionMet(is, numericValueToConcreteAssignment);
        if(result != -1 ){
            Unit target_unit = is.getTarget();
            if(target_unit==null){
                Utils.generatePartingLine("!");
                System.out.println("Cannot find the target Unit of the IfStmt: " + is);
                Utils.generatePartingLine("!");
                exit(0);
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
                    Log.logData(log_file, Utils.generatePartingLine("+"));
                    Log.logData(log_file, "Case value: " + case_value + " => " + case_id);
                    Log.logData(log_file, "Target unit (hash code): " + target_unit.hashCode());
                    Log.logData(log_file, "Next block head (hash code): " + next_block_head.hashCode());
                    Log.logData(log_file, Utils.generatePartingLine("+"));
                    // If the next block's first Unit is not the target Unit, this path is incorrect.
                    if (!next_block_head.equals(target_unit)) {
                        return true;
                    }
                }
            } else {
                Utils.generatePartingLine("!");
                System.out.println("Cannot find the target Unit of the case ID [ " + case_id + " ].");
                System.out.println("SwitchStmt: " + lss);
                Utils.generatePartingLine("!");
                exit(0);
            }
        } else {
            Utils.generatePartingLine("!");
            System.out.println("Cannot find the corresponding case ID of the case value [ " + case_value + " ].");
            Utils.generatePartingLine("!");
            exit(0);
        }
        return false;
    }

    public static Value hasRedefinedValue(AssignStmt as, InvokeExpr ie, List<Value> tainted_values, Unit tainted_unit){

        Value v = Utils.hasLeftValueOfAssignStmt(as, tainted_values);
        if (v != null) {
            if (tainted_unit != null && as.toString().equals(tainted_unit.toString())) return null;

            if (ie != null && ie.getMethod().getDeclaringClass().toString().equals("android.content.pm.parsing.result.ParseInput"))
                return null;

            if(v.getType().toString().equals("boolean")){
                if(as.getUseBoxes().size()==1 && (as.getRightOp() instanceof IntConstant)){ // Assign 0 or 1 to this boolean value directly.
                    return null;
                }
            }

            return v;
        }
        return null;
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

    public static String confirmTaintedItemOfMap(String method_name, Set<Integer> tainted_param_indices){
        System.out.println("Map: " + method_name + " => " + tainted_param_indices);
        if(method_name == null || tainted_param_indices == null) {
            return null;
        }
        String item = "";
        if(method_name.equals("add")){
            if(tainted_param_indices.contains(1)){
                item += "_key";
            }
            if(tainted_param_indices.contains(2)){
                item += "_value";
            }
        } else if(method_name.equals("put")){
            if(tainted_param_indices.contains(0)){
                item += "_key";
            }
            if(tainted_param_indices.contains(1)){
                item += "_value";
            }
        }
        return item;
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

    public static String getDataStructure(Value data_structure, Map<Value, String> mapValueToTaintedItem){
        if (data_structure == null) {
            return null;
        }
        String structure;
        if (data_structure.toString().contains(".<")) {
            structure = data_structure.toString();
        } else {
            structure = data_structure.getType().toString();
        }
        if(structure.contains("Map")){ // For the Map value, we need know whether the key or value is tainted.
            String item = mapValueToTaintedItem.get(data_structure);
            if(item!=null) {
                structure += item;
            }else{
                Utils.printPartingLine("!");
                System.out.println("Cannot find the tainted item of the Map value: " + data_structure);
                Utils.printPartingLine("!");
                exit(0);
            }
        }
        return structure;
    }

    public static SootMethod getImplementedMethodOfAbstractMethod(String log_file, InterfaceInvokeExpr ifi, Tainted tainted_point){
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
        Log.logData(log_file, "--- abstract class: " + interface_cls);
        Log.logData(log_file, "--- abstract method: " + abstract_method.getSignature());

        // Find the corresponding implemented classes.
        // If this interface class does not have its implemented class or implemented method,
        // analyze its sub interface classes;
        Set<SootClass> implemented_classes = Utils.interfaceClassToImplementedClasses.get(interface_cls);
        Set<SootClass> sub_interface_classes = Utils.interfaceClassToSubInterfaceClasses.get(interface_cls);
        while(implemented_classes == null) {
            if(sub_interface_classes==null || sub_interface_classes.isEmpty()){
                break;
            }
            for (SootClass i_cls : sub_interface_classes) {
                implemented_classes = Utils.interfaceClassToImplementedClasses.get(i_cls);
                if (implemented_classes != null) {
                    break;
                }
                sub_interface_classes.remove(i_cls);
                Set<SootClass> sub_classes = Utils.interfaceClassToSubInterfaceClasses.get(i_cls);
                if(sub_classes!=null){
                    sub_interface_classes.addAll(sub_classes);
                }
            }
        }
        if(implemented_classes == null) {
            Utils.printPartingLine("!");
            System.out.println("Special abstract class. Cannot find the implemented class of " + interface_cls.getName());
            Utils.printPartingLine("!");
            return null;
        }

        SootClass implemented_cls = null;
        if (implemented_classes.size() == 1) {
            implemented_cls = implemented_classes.iterator().next();
        } else {
            Log.logData(log_file, Utils.generatePartingLine("~"));
            Log.logData(log_file, "Multiple implemented classes, try to confirm the concrete one ... ");
            //System.out.println(implemented_classes);
            int flag_found = 0;
            if (base != null && tainted_point != null) {
                List<Tainted> path = Utils.deepCopy(tainted_point.getParents());
                path.add(tainted_point);
                // Find the creation of the base value to confirm the implemented class.
                for (int i = path.size(); i > 0; i--) {
                    Tainted point = path.get(i - 1);
                    Map<Value, Integer> parameters = point.getParameters();
                    if (parameters != null && parameters.get(base) != null) { // If the base is a parameter of the method, we need analyze its parent.
                        if (i - 1 > 0) {
                            // Transform the base value.
                            Body body = path.get(i - 2).getMethod().retrieveActiveBody();
                            for (Unit unit : body.getUnits()) {
                                if (unit.equals(point.getCallUnit())) {
                                    base = Utils.getInvokeOfUnit(unit).getArg(parameters.get(base));
                                    break;
                                }
                            }
                        }
                    } else { // The base is defined in this method.
                        implemented_cls = findCreationOfClassObject(point.getMethod().retrieveActiveBody(), base);
                        if (implemented_cls != null) {
                            flag_found = 1;
                            Log.logData(log_file, "Confirmed!");
                        }
                        break;
                    }
                }
            }
            if (flag_found == 0) {
                SootClass declaring_cls = ((RefType) base.getType()).getSootClass();
                if (implemented_classes.contains(declaring_cls)) {
                    implemented_cls = declaring_cls;
                    Log.logData(log_file, "Cannot confirm (base =  " + base + "), choose the the base's declaring class");
                } else {
                    implemented_cls = implemented_classes.iterator().next();
                    Log.logData(log_file, "Cannot confirm (base =  " + base + "), choose the first.");
                }
            }
            Log.logData(log_file, Utils.generatePartingLine("~"));
        }
        Log.logData(log_file, "--- implemented class: " + implemented_cls);

        // Find the implemented method.
        while (true) {
            for (SootMethod method : implemented_cls.getMethods()) {
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
                                        Log.logData(log_file, "--- implemented method: " + implemented_method.getSignature());
                                        return implemented_method;
                                    }
                                }
                            }
                        }
                        //System.out.println("--- implemented method: " + method.getSignature());
                        Log.logData(log_file, "--- implemented method: " + method.getSignature());
                        return method;
                    }
                }
            }
            // If this implemented class does not have the implemented method,
            // analyze its parent class.
            implemented_cls = implemented_cls.getSuperclass();
            if (implemented_cls == null) {
                break;
            }
        }

        Utils.printPartingLine("!");
        System.out.println("Special abstract method. Cannot find the implemented method of " + abstract_method.getSignature());
        Utils.printPartingLine("!");
        return null;
    }

    // Store the byte value's concrete assignment.
    // For the case ID transform of the two associated switch-case statements.
    public static void storeNumericValueAndCorrespondingConcreteAssignment(AssignStmt as, Map<Value, String> numericValueToConcreteAssignment){
        Value def_value = as.getLeftOp();
        InvokeExpr ie = Utils.getInvokeOfAssignStmt(as);
        if(!def_value.getUseBoxes().isEmpty()) return;
        List<ValueBox> vbs = as.getUseBoxes();
        if("int_byte_boolean".contains(def_value.getType().toString())){
            if(vbs.size() == 1){
                Value use_value = as.getRightOp();
                if(use_value instanceof IntConstant){ // Concrete assignment.
                    numericValueToConcreteAssignment.put(def_value, use_value.toString());
                } else { // b1 = b2
                    String assign = numericValueToConcreteAssignment.get(use_value);
                    numericValueToConcreteAssignment.put(def_value, assign);
                }
            } else if(ie!=null) { // b1 is the return value of a method.
                numericValueToConcreteAssignment.put(def_value, null);
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
                            System.out.println(Utils.generatePartingLine("!"));
                            System.out.println("Computing Error: " + s);
                            System.out.println(Utils.generatePartingLine("!"));
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

    public static void storeMapValueAndCorrespondingTaintedItem(Value map_value, String tainted_item, Map<Value, String> mapValueToTaintedItem, Map<Value, Value>newValueToCopy){
        mapValueToTaintedItem.put(map_value, tainted_item);
        if(!map_value.getUseBoxes().isEmpty()){
            map_value = map_value.getUseBoxes().get(0).getValue();
        }
        if(newValueToCopy.containsKey(map_value)){
            mapValueToTaintedItem.put(newValueToCopy.get(map_value), tainted_item);
        }
    }

    public static void removePreviouslyTaintedValue(Value pre_tainted_value, List<Value> tainted_values, Map<Value, Value> newValueToCopy){
        int index = tainted_values.indexOf(pre_tainted_value);
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
        if(tainted_values.contains(new_tainted_value)) return;
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
}
