package analysis;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class BU { // Base analysis unit.
    private SootMethod mBaseMethod;
    private String mAssociatedElementType;
    private Unit mCallUnit; // The invocation statement that generate this BU.
    private Unit mStartUnit; // The first noteworthy statement. Analyze to confirm.
    private Set<BU> mPassingChildren; // The passing callee of this base method. Analyze to confirm.
    private Set<Integer> mEntryBUParamIndies;
    private Set<Integer> mInflowParamIndices;
    private Set<Integer> mIdentifierParamIndices;
    private Set<Integer> mNullParamIndices;
    private List<Pair<String, String>> mAssociatedElementTypesAndDataStructures; // The data structure info. Analyze to confirm.
    private List<BU> mParents;
    private List<Value> mSourceVariables; // For entry bast-units.
    private Map<Integer, Value> mInflowStruParaIndexToSupportingObj;
    private Map<Integer, String> mInflowMapParamIndexToInflowItem;
    private Map<Integer, String> mParamIndexToField;
    private Map<Integer, String> mParamIndexToElementType;
    private Map<Integer, String> mParamIndexToNumericValue;
    private Map<Value, Integer> mParameterToIndex; // Analyze to confirm.
    private Map<AssignStmt, String> mSourceDefToElementType; // May need to analyze to confirm.


    public BU(SootMethod base_method, String associated_element_type, Unit call_unit, List<BU> parents, Set<Integer> entryBU_param_indices,
              Set<Integer> identifier_param_indices, Set<Integer> inflow_param_indices, Set<Integer> null_param_indices,
              Map<Integer, String> inflowMapParamIndexToInflowItem, Map<Integer, Value> inflowStruParaIndexToSupportingObj,
              Map<Integer, String> paramIndexToElementType, Map<Integer, String> paramIndexToFiled,
              Map<Integer, String> paramIndexToNumericValue) {
        mBaseMethod = base_method;
        mAssociatedElementType = associated_element_type;
        mCallUnit = call_unit;
        mParents = parents;
        mEntryBUParamIndies = entryBU_param_indices;
        mIdentifierParamIndices = identifier_param_indices;
        mInflowParamIndices = inflow_param_indices;
        mNullParamIndices = null_param_indices;
        mInflowMapParamIndexToInflowItem = inflowMapParamIndexToInflowItem;
        mInflowStruParaIndexToSupportingObj = inflowStruParaIndexToSupportingObj;
        mParamIndexToElementType = paramIndexToElementType;
        mParamIndexToField = paramIndexToFiled;
        mParamIndexToNumericValue = paramIndexToNumericValue;
    }

    public BU(SootMethod method, List<Value> source_vars){
        mBaseMethod = method;
        mSourceVariables = source_vars;
    }

    public BU(SootMethod method){
        mBaseMethod = method;
    }

    public SootMethod getBaseMethod(){
        return mBaseMethod;
    }

    public Set<Integer> getInflowParamIndices(){
        return mInflowParamIndices;
    }

    public List<Value> getSourceVariables(){
        return mSourceVariables;
    }
    public String getAssociatedElementType(){
        return mAssociatedElementType;
    }

    public List<BU> getParents(){
        return mParents;
    }

    public Unit getCallUnit(){
        return mCallUnit;
    }

    public Unit getStartUnit(){
        return mStartUnit;
    }

    public Set<BU> getPassingChildren(){
        return mPassingChildren;
    }

    public List<Pair<String, String>> getAssociatedElementTypesAndDataStructures(){
        return mAssociatedElementTypesAndDataStructures;
    }

    public Map<Value, Integer> getParameters(){
        return mParameterToIndex;
    }

    public Set<Integer> getEntryBUParamIndies(){
        return mEntryBUParamIndies;
    }

    public Set<Integer> getIdentifierParamIndices(){
        return mIdentifierParamIndices;
    }

    public Set<Integer> getNullParamIndices(){
        return mNullParamIndices;
    }

    public Map<Integer, String> getElementTypeParamIndies(){
        return mParamIndexToElementType;
    }

    public Map<Integer, String> getFieldParamIndies(){
        return mParamIndexToField;
    }

    public Map<Integer, Value> getInflowStruParamIndies(){
        return mInflowStruParaIndexToSupportingObj;
    }
    public Map<Integer, String> getInflowMapParamIndies(){
        return mInflowMapParamIndexToInflowItem;
    }

    public Map<Integer, String> getNumericParamIndies(){
        return mParamIndexToNumericValue;
    }

    public Map<AssignStmt, String> getSourceDefs(){
        return mSourceDefToElementType;
    }

    public void setBaseMethod(SootMethod method){
        mBaseMethod = method;
    }

    public void setBaseElement(String element){
        mAssociatedElementType = element;
    }
    public void setSourceVariables(List<Value> source_variables){
        mSourceVariables = source_variables;
    }
    public void setStartUnit(Unit start_unit){
        mStartUnit = start_unit;
    }

    public void storeAssociatedElementTypeAndDataStructure(String[] log_files, String associated_element_type, String data_structure) {
        String analysis_data = log_files[0];
        String method_data = log_files[1];
        Log.logData(analysis_data, Utils.generatePartingLine("~"));
        Log.logData(analysis_data, "- Associated Element type: " + associated_element_type);
        Log.logData(analysis_data, "- Data structure: " + data_structure);
        Log.logData(analysis_data, Utils.generatePartingLine("~"));


        Pair<String, String> e_d = new Pair<String, String>(associated_element_type, data_structure);
        if (mAssociatedElementTypesAndDataStructures == null) {
            mAssociatedElementTypesAndDataStructures = new ArrayList<>();
        }
        if(!mAssociatedElementTypesAndDataStructures.contains(e_d)) { // Avoid duplicated logs.
            mAssociatedElementTypesAndDataStructures.add(e_d);
            // analysis.Log data.
            Log.logData(method_data, Utils.generatePartingLine("="));
            Log.logData(method_data, "+ Associated Element type: " + associated_element_type);
            Log.logData(method_data, "+ Data structure: " + data_structure);
        }
    }

    public void setAssociatedElementTypesAndDataStructures(List<Pair<String, String>> e_ds){
        mAssociatedElementTypesAndDataStructures = e_ds;
    }

    public void storePassingChild(BU child){
        if(child == null) return;

        if(mPassingChildren ==null){
            mPassingChildren =new HashSet<>();
            mPassingChildren.add(child);
        } else {
            mPassingChildren.add(child);
        }
    }

    public void setPassingChildren(Set<BU> children){
        mPassingChildren = children;
    }

    public void storeParameter(Value param, Integer index){
        if(index < 0 || param == null) return;

        if(mParameterToIndex == null){
            mParameterToIndex = new HashMap<>();
        }
        mParameterToIndex.put(param, index);
    }

    public void setParameters(Map<Value, Integer> paramToIndex){
        mParameterToIndex = paramToIndex;
    }


    public void storeSourceDef(AssignStmt as, String element_type){
        if(mSourceDefToElementType == null){
            mSourceDefToElementType = new HashMap<>();
        }
        mSourceDefToElementType.put(as, element_type);
    }

    public void setSourceDefs(Map<AssignStmt, String> sourceDefToElementType){
        mSourceDefToElementType = sourceDefToElementType;
    }

    public void setEntryBUParamIndices(Set<Integer> entryBU_param_indices){
        mEntryBUParamIndies = entryBU_param_indices;
    }
}
