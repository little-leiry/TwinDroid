import com.sun.org.apache.xpath.internal.operations.Bool;
import soot.*;
import soot.jimple.*;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class Tainted {
    // The tainted_methods needed to be analysed.
    // Use queue to do BFS.
    public static Queue<Pair<SootMethod, Value>> tainted_methods = new LinkedList<Pair<SootMethod, Value>>();
    public static Queue<String> test = new LinkedList<String>();

    // For constructing the call path of the given method.
    // method => parents
    public static Map<SootMethod, Set<SootMethod>> methodToParents = new HashMap<SootMethod, Set<SootMethod>>();
    // element name => data structures.
    public static Map<String, Set<Value>> elementToDataStructures = new HashMap<String, Set<Value>>();
    // element name => the method for parsing the element.
    public static Map<String, SootMethod> elementToMethod = new HashMap<String, SootMethod>();
    // method name => List of Pair<element name, data structure>
    public static Map<SootMethod, Set<Pair<String, Value>>> methodToElement_DataStructures = new HashMap<SootMethod, Set<Pair<String, Value>>>();
    // One call path of a given method.
    public static List<String> call_path = new ArrayList<>();
    // All call paths of analyzed methods.
    public static List<List<String>> call_paths = new ArrayList<>();

    public static final String log_file = "log_data.txt";

    public Tainted(){}

    // ParseResult<ParsedPermission> result = ParsedPermissionUtils.parsePermission(
    //          pkg, res, parser, sUseRoundIcon, input);
    public static boolean isTaintedByEntryPoint(AssignStmt as, Value entry){
        if (as.containsInvokeExpr()) {
            Value left = as.getLeftOp();
            InvokeExpr i = as.getInvokeExpr();
            if (Utility.isParameter(i, entry) != -1) {
                if (left.getType().toString().equals("android.content.pm.parsing.result.ParseResult")){
                    return true;
                }
            }
        }
        return false;
    }

/*    public static Boolean containTaintedValue(Unit unit, Value tainted_value){
        //parameter of the Invoke statement
        if(unit instanceof InvokeStmt){
            InvokeExpr i = (InvokeExpr) unit;
            return Utility.isParameter(i, tainted_value)!=-1;
        }
        //used value of the assignment statement
        if(unit instanceof AssignStmt){
            AssignStmt as = (AssignStmt) unit;
            return Utility.containValue(as, tainted_value);
        }
        return false;
    }*/

    public static void generateCallPathsAndLogData(SootMethod method, Value data_structure, int flag){
        if(flag == 0) { // Only consider the nearest elements.
            if (elementToMethod.containsValue(method)){
                List<String> elements = getElementsOfMethod(method, null);
                for(String e: elements){
                    storeElementAndCorrespondingDataStructure(e, data_structure);
                }
                Store.logData(log_file, "element(s):");
                Store.logData(log_file, elements.toString());
                Store.logData(log_file, "data structure:");
                if (data_structure.toString().contains(".<")) { // r0.<android.content.pm.parsing.component.ParsedComponent: java.util.List intents> = $r2
                    Store.logData(log_file, data_structure.toString());
                } else {
                    Store.logData(log_file, data_structure.getType().toString());
                }
                flag = 1;
            }
        }

        call_path.add(method.getSignature());
        if(methodToParents.containsKey(method)){
            Set<SootMethod> parents = methodToParents.get(method);
            for(SootMethod p : parents){
                generateCallPathsAndLogData(p, data_structure, flag);
            }
            call_path.remove(method.getSignature());
        }else{
            // Store the call path when the method have no parent.
            List<String> call_path_reverse = new ArrayList<>();
            for(int i = call_path.size(); i > 0; i--){
                call_path_reverse.add(call_path.get(i-1));
            }
            if (!call_paths.contains(call_path_reverse)) {
                call_paths.add(call_path_reverse);
                // log
                Store.logData(log_file, "call path:");
                Store.logData(log_file, call_path_reverse.toString());
            }
            call_path.remove(method.getSignature());
        }
    }


    public static List<String> getElementsOfMethod(SootMethod method, List<String> referred_elements){
        List<String> elements = new ArrayList<>(); //One method may correspond to multiple elements.
        if(method==null) return elements;
        if(elementToMethod.containsValue(method)){
            for(Map.Entry<String, SootMethod> entry : elementToMethod.entrySet()){
                if(method.equals(entry.getValue())){
                    if(referred_elements != null){ // Filter some unsuitable results.
                        if(referred_elements.contains(method)){
                            elements.add(entry.getKey());
                        }
                    } else {
                        elements.add(entry.getKey());
                    }

                }
            }
        }
        return elements;
    }

    public static void storeElementAndCorrespondingMethod (String element, SootMethod method){
        // Normal situation: one element corresponds to one parsing method.
        if(!elementToMethod.containsKey(element)){
            elementToMethod.put(element, method);
            System.out.println(element + " => " + method.getName());
        } else{ // Strange situation: one element may have different parsing methods.
            SootMethod old_method = elementToMethod.get(element);
            if(! old_method.equals(method)) {
                Utility.printSymbols("!");
                System.out.println("The corresponding method of this element already exists: " + element + " => " + elementToMethod.get(element));
                System.out.println("Current method is " + method.getName());
                Utility.printSymbols("!");
            }
        }
    }

    public static void storeElementAndCorrespondingDataStructure(String element, Value data_structure){
        Set<Value> ds = elementToDataStructures.get(element);
        if (ds == null) { // This key does not exist.
            ds = new HashSet<>();
            ds.add(data_structure);
            elementToDataStructures.put(element, ds);
            } else {
            ds.add(data_structure);
        }
    }
    public static void storeMethodAndCorrespondingElement_DataStructure(SootMethod method, String element, Value data_structure){
        Set<Pair<String, Value>> e_ds = methodToElement_DataStructures.get(method);
        Pair<String, Value> e_d = new Pair<String, Value>(element, data_structure);
        if(e_ds == null) { // This key does not exist.
            e_ds = new HashSet<>();
            e_ds.add(e_d);
            methodToElement_DataStructures.put(method, e_ds);
        } else { // Avoid duplicate keys.
            e_ds.add(e_d);
        }
    }

    public static void findEntryPoints() {
        //Map<SootMethod, Value> entries = new HashMap<SootMethod,Value>();
        String className = "android.content.pm.parsing.ParsingPackageUtils"; // the class for parsing an apk
        List<SootMethod> methods = Utility.getMethodsOfClass(className);
        for (SootMethod sm : methods) {
            if (sm.isConcrete()) {
                Body body = sm.retrieveActiveBody();
                for (Unit unit : body.getUnits()) {
                    if (unit instanceof AssignStmt) {
                        AssignStmt as = (AssignStmt) unit;
                        InvokeExpr callee = Utility.getInvokeOfAssignStmt(as);
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
                                            tainted_methods.offer(new Pair<SootMethod, Value>(sm, entry));
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
    public static void dataFlowAnalysisForMethod(SootMethod entry_method, Value entry_value, List<String> skip_methods, List<String> no_analyzed_methods, List<String> skip_classes, List<String> no_analyzed_classes){
        String element = "NULL";
        int flag_element = 0;
        int count = 0;
        int case_num = 0;
        Value case_value = null;
        Map<Value, String> valueToLikelyElement = new HashMap<Value, String>();
        Map<String, String> caseIdToElement = new HashMap<String, String>();
        List<String> elements=new ArrayList<>(); // Involving elements in this method.
        Value data_structure = null;
        Value tainted_value = null;
        SootMethod parseMethod = null;
        int pass_tainted_value = 1;
        Body body = null;
        if(entry_method.isConcrete()) {
            body = entry_method.retrieveActiveBody();
        } else {
            Utility.printSymbols("!");
            System.out.println("The method " + entry_method.getSignature() + " does not have a body.");
            return;
        }
        for(Unit unit:body.getUnits()){
            InvokeExpr i = null;
            Value base = null;
            String base_type = "NULL";
            SootMethod callee = null;
            String callee_name = "NULL";
            String declaring_class = "NULL";
            int need_analysis = 0;
            int assignStmt = 0;
            // Get the mapping relationship of elements and methods.
            // For the switch-case situation:
            // switch(element)-case(XXX)=>parseXXX(parser):
            // LookupSwitchStmt($i1){case -12356 goto z0 = equals(XXX), b2 = 0}
            // LookupSwitchStmt(b2){case 0 goto $r6 = parseXXX(parser)}
            if(unit instanceof LookupSwitchStmt){
                LookupSwitchStmt lss = (LookupSwitchStmt) unit;
                for(int num =0; num< lss.getTargetCount();num++){
                    Unit u = lss.getTarget(num);
                    InvokeExpr invoke = Utility.getInvokeOfUnit(u);
                    if (invoke != null) {
                        SootMethod sm = invoke.getMethod();
                        if (sm.getName().equals("equals")) { // This LookupSwitchStmt is related to elements.
                            case_num = lss.getTargetCount(); // The number of elements.
                            break;
                        }
                        if (case_value !=null) {
                            if (lss.getUseBoxes().get(0).getValue().equals(case_value)) { // This LookupSwitchStmt is corresponding to the element's LookupSwitchStmt.
                                String case_id = ((Integer) lss.getLookupValue(num)).toString();
                                if (caseIdToElement.containsKey(case_id)) {
                                    String e = caseIdToElement.get(case_id);
                                    storeElementAndCorrespondingMethod(e, sm);
                                }
                            }
                        }
                    }
                }
            }

            // A statement needs to be analysed only if it contains the entry / tainted value.
            if(unit instanceof AssignStmt) {
                assignStmt = 1;
                AssignStmt as = (AssignStmt) unit;
                i = Utility.getInvokeOfAssignStmt(as);
                if (Utility.isUsedValueOfAssignment(as, entry_value) || Utility.isUsedValueOfAssignment(as, tainted_value)) {
                    need_analysis = 1;
                }
                if(as.getUseBoxes().get(0).getValue() instanceof StringConstant){ // This statement is likely related to an element.
                    Value element_value = as.getLeftOp();
                    String likely_element = as.getUseBoxes().get(0).getValue().toString();
                    valueToLikelyElement.put(element_value, likely_element);
                    Utility.printSymbols("+");
                    System.out.println("Likely element: " + as);
                    Utility.printSymbols("+");
                }
            } else if (unit instanceof InvokeStmt) {
                i = ((InvokeStmt) unit).getInvokeExpr();
                if (Utility.isParameter(i, entry_value) != -1 || Utility.isParameter(i, tainted_value) != -1) {
                    need_analysis = 1;
                }
            }

            if(i!=null) {
                callee = i.getMethod();
                callee_name = callee.getName();
                base = Utility.getBaseOfInvokeExpr(i);
            }

            // Get the element's name.
            if(callee_name.equals("equals")){
                if (i.getArg(0) instanceof StringConstant){ // parser.getName().equals(element)
                    element = i.getArg(0).toString();
                } else if (base != null){ // element.equals(parser.getName())
                    if(valueToLikelyElement.containsKey(base)){
                        element=valueToLikelyElement.get(base);
                    }
                }
                elements.add(element);
                flag_element = 1;
            }

            if(flag_element == 1 && case_num!=0){ // The switch-case situation of multiple elements.
                count += 1;
                // Get the mapping relationship of two related LookupSwitchStmts' case IDs
                if (count == 3) {
                    if (assignStmt == 1){
                        AssignStmt as = (AssignStmt) unit;
                        String case_id = as.getUseBoxes().get(0).getValue().toString();
                        if(Utility.isNumeric(case_id)) {
                            if (case_value == null) {
                                case_value = as.getLeftOp();
                            }
                            System.out.println(case_id + " => " + element);
                            caseIdToElement.put(case_id, element);
                        } else {
                            Utility.printSymbols("!");
                            System.out.println("Special case id: " + unit);
                            Utility.printSymbols("!");
                        }
                    } else {
                        Utility.printSymbols("!");
                        System.out.println("Special case: " + unit);
                        Utility.printSymbols("!");
                        // There is a default case ID.
                        List<String> case_ids = Utility.intToList(case_num);
                        for(String case_id : case_ids){
                            if(!caseIdToElement.containsKey(case_id)){
                                System.out.println(case_id + " => " + element);
                                caseIdToElement.put(case_id, element);
                            }
                        }
                    }
                    // This element case has been solved, reset the element's initial value, flag and counter.
                    element = "NULL";
                    flag_element=0;
                    count=0;
                }
            }

            if (need_analysis == 0) continue;
            Utility.printSymbols("-");
            System.out.println("unit: " + unit);
            System.out.println("entry value: " + entry_value);
            if(tainted_value!=null) {
                System.out.println("tainted value: " + tainted_value);
            }
            Utility.printSymbols("-");

            // result = XXX(parser)
            // Multiple parsed results.
            if (entry_value.getType().toString().equals("android.content.res.XmlResourceParser")){
                if(Utility.isParameter(i, entry_value) != -1){
                    if(! skip_methods.contains(callee_name)){
                        if (flag_element == 1 && case_num == 0){ // Other situations of elements.
                            storeElementAndCorrespondingMethod(element, callee);
                            // This element case has been solved, reset the element's initial value and flag.
                            element = "NULL";
                            flag_element = 0;
                        }
                        if (tainted_value !=null && !tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")) {  // Have solved one parsed result.
                            data_structure = tainted_value;
                            List<String> es = getElementsOfMethod(parseMethod, elements); // The obtained elements are related to the parse method and the entry method.
                            for (String e : es) {
                                storeElementAndCorrespondingDataStructure(e, data_structure);
                                storeMethodAndCorrespondingElement_DataStructure(entry_method, e, data_structure);
                            }
                        }
                        // Initialize or reset the tainted value.
                        tainted_value = entry_value;
                        // Initialize or Update the parse method.
                        parseMethod = callee;
                    }
                }
            }

            // Treat the tainted value as a whole, ignore the parts (i.e., the attributions) of it.
            if(base!=null) {
                base_type = base.getType().toString();
                if (base.equals(tainted_value)) {
                    Utility.printSymbols("*");
                    System.out.println("tainted base: " + unit);
                    Utility.printSymbols("*");
                    if (base_type.equals("android.content.pm.parsing.result.ParseResult")) {
                        if (!callee_name.equals("getResult")) { // ! result.getResult()
                            continue;
                        } else {
                            pass_tainted_value = 1;
                        }
                    } else{
                        if (!callee_name.startsWith("to")) continue; // ! tainted_value.toBundle()
                    }
                }
            }

            // If the tainted value is passed in the callee, this callee is tainted.
            Integer parameter_index = Utility.isParameter(i, tainted_value);
            if(parameter_index!=-1){
                Utility.printSymbols("*");
                System.out.println("tainted callee: " + unit);
                Utility.printSymbols("*");
                declaring_class = callee.getDeclaringClass().getName();
                if(callee_name.equals("add") || callee_name.equals("put")){ // xxx.add(tainted_value)
                    if(base!=null) {
                        tainted_value = base;
                        continue;
                    }
                }
                if(skip_methods.contains(callee_name) || skip_classes.contains(declaring_class)) continue;
                if(callee_name.startsWith("is")) continue;
                if(! no_analyzed_methods.contains(callee_name) && ! no_analyzed_classes.contains(declaring_class)){
                    Value parameter = Utility.getParameter(callee, parameter_index);
                    if(parameter!=null) {
                        tainted_methods.offer(new Pair<SootMethod, Value>(callee, parameter));
                        Set<SootMethod> parents = methodToParents.get(callee);
                        if (parents == null) { // This key is not exist.
                            parents = new HashSet<>();
                            parents.add(entry_method);
                            methodToParents.put(callee, parents);
                        } else { // Avoid duplicated parents.
                            parents.add(entry_method);
                        }
                    } else{
                        Utility.printSymbols("!");
                        System.out.println("Special parameter.");
                        System.out.println("method: " + callee.getSignature());
                        System.out.println("parameter index: " + parameter_index);
                        Utility.printSymbols("!");
                    }
                }
            }

            // Pass the tainted value.
            if(assignStmt == 1 && pass_tainted_value == 1){
                AssignStmt as = (AssignStmt) unit;
                // r6 = (java.util.Set) $r10
                // $r7 = r11.<android.content.pm.parsing.component.ParsedProcess: java.lang.String name>
                if(i==null && as.getUseBoxes().size() == 2){
                    if(as.getUseBoxes().get(0).toString().contains(".<")) continue;
                }
                tainted_value = ((AssignStmt) unit).getLeftOp();
                if (tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")){
                    pass_tainted_value = 0; // Only result.getResult can be passed, when the tainted value is the type of ParseResult.
                }
            }
        }
        if(!element.equals("NULL")){
            Utility.printSymbols("!");
            System.out.println("Special element : " + element + " in the method " + entry_method.getSignature());
            storeElementAndCorrespondingMethod(element, entry_method);
            Utility.printSymbols("!");
        }

        if(tainted_value!=null && tainted_value.getType().toString().equals("android.content.pm.parsing.result.ParseResult")){
            data_structure = tainted_value;
            if (parseMethod != null){ // The last parsed result.
                List<String> es = getElementsOfMethod(parseMethod, elements);
                for(String e: es) {
                    storeElementAndCorrespondingDataStructure(e, data_structure);
                    storeMethodAndCorrespondingElement_DataStructure(entry_method, e, data_structure);
                }
            } else {
                Pair<String, Value> e_d = new Pair<String, Value>(element, tainted_value);
                Set<Pair<String, Value>> e_ds = methodToElement_DataStructures.get(entry_method);
                if (e_ds == null) {
                    e_ds = new HashSet<>();
                    e_ds.add(e_d);
                    methodToElement_DataStructures.put(entry_method, e_ds);
                } else {
                    e_ds.add(e_d);
                }
            }
        }
        // log
        Set<Pair<String, Value>> e_ds = methodToElement_DataStructures.get(entry_method);
        if(e_ds!=null){
            for(Pair<String, Value> e_d : e_ds){
                String e = e_d.getO1();
                Value d = e_d.getO2();
                if(!e.equals("NULL")){
                    Store.logData(log_file, "element:");
                    Store.logData(log_file, e);
                    generateCallPathsAndLogData(entry_method, d, 0);
                } else {
                    generateCallPathsAndLogData(entry_method, d, 1);
                    Store.logData(log_file, "data structure:");
                    if (data_structure.toString().contains(".<")) { // r0.<android.content.pm.parsing.component.ParsedComponent: java.util.List intents> = $r2
                        Store.logData(log_file, data_structure.toString());
                    } else {
                        Store.logData(log_file, data_structure.getType().toString());
                    }
                }
            }
        }
    }
}
