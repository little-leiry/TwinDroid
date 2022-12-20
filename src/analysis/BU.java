package analysis;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class BU { // Base analysis unit.
    private SootMethod mMethod;
    private String mOuterElement;
    private Unit mCallUnit;
    private Unit mStartUnit;
    private Set<Integer> mTaintedAttributes;
    private Set<AssignStmt> mEntryAssigns;
    private Set<BU> mTaintedChildren;
    private Set<Integer> mTaintedParamIndices;
    private List<String> mDataStructures;
    private List<Pair<String, String>> mInnerElementsAndStructures;
    private List<BU> mParents;
    private List<Value> mTaintedValues;
    private Map<Value, Integer> mParameters;
    private Map<Integer, String> mTaintedMapItem;

    public BU(SootMethod method, Set<Integer> param_indices, String element, List<BU> parents, Unit call_unit, Map<Integer, String> mapItem) {
        mMethod = method;
        mTaintedParamIndices = param_indices;
        mOuterElement = element;
        mParents = parents;
        mCallUnit = call_unit;
        mTaintedMapItem = mapItem;
    }

    public BU(SootMethod method, Set<Integer> param_indices, String element, Unit call_unit, Map<Integer, String> mapItem){
        mMethod = method;
        mTaintedParamIndices = param_indices;
        mOuterElement = element;
        mCallUnit = call_unit;
        mTaintedMapItem = mapItem;
    }

    public BU(SootMethod method, Set<Integer> param_indices, Unit call_unit, Map<Integer, String> mapItem){
        mMethod = method;
        mTaintedParamIndices = param_indices;
        mCallUnit = call_unit;
        mTaintedMapItem = mapItem;
    }

    public BU(SootMethod method, List<Value> values){
        mMethod = method;
        mTaintedValues = values;
    }

    public BU(SootMethod method){
        mMethod = method;
    }

    public BU(){}

    public SootMethod getMethod(){
        return mMethod;
    }

    public Set<Integer> getTaintedParamIndices(){
        return mTaintedParamIndices;
    }

    public List<Value> getTaintedValues(){
        return mTaintedValues;
    }
    public String getOuterElement(){
        return mOuterElement;
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

    public Set<BU> getTaintedChildren(){
        return mTaintedChildren;
    }

    public List<Pair<String, String>> getInnerElementAndStructures(){
        return mInnerElementsAndStructures;
    }

    public Map<Value, Integer> getParameters(){
        return mParameters;
    }

    public List<String> getDataStructures(){
        return mDataStructures;
    }

    public Map<Integer, String> getTaintedMapItem(){
        return mTaintedMapItem;
    }

    public Set<AssignStmt> getEntryAssigns(){
        return mEntryAssigns;
    }

    public Set<Integer> getTaintedAttributes(){
        return mTaintedAttributes;
    }
    public void setMethod(SootMethod method){
        mMethod = method;
    }

    public void setOuterElement(String element){
        mOuterElement = element;
    }
    public void setTaintedValues(List<Value> tainted_values){
        mTaintedValues = tainted_values;
    }
    public void setStartUnit(Unit start_unit){
        mStartUnit = start_unit;
    }

    public void storeInnerElementAndStructure(String element, String data_structure) {
        Log.logData(AnalysisForParsingClass.analysis_data, Utils.generatePartingLine("~"));
        Log.logData(AnalysisForParsingClass.analysis_data, "- Element: " + element);
        Log.logData(AnalysisForParsingClass.analysis_data, "- Data structure: " + data_structure);
        Log.logData(AnalysisForParsingClass.analysis_data, Utils.generatePartingLine("~"));


        Pair<String, String> e_d = new Pair<String, String>(element, data_structure);
        if (mInnerElementsAndStructures == null) {
            mInnerElementsAndStructures = new ArrayList<>();
        }
        if(!mInnerElementsAndStructures.contains(e_d)) { // Avoid duplicated logs.
            mInnerElementsAndStructures.add(e_d);
            // analysis.Log data.
            Log.logData(AnalysisForParsingClass.method_data, Utils.generatePartingLine("="));
            Log.logData(AnalysisForParsingClass.method_data, "+ Element: " + element);
            Log.logData(AnalysisForParsingClass.method_data, "+ Data structure: " + data_structure);
        }
    }

    public void storeInnerElementAndStructure2(String element, String data_structure) {
        Log.logData(AnalysisForParsingClass2.analysis_data, Utils.generatePartingLine("~"));
        Log.logData(AnalysisForParsingClass2.analysis_data, "- Element: " + element);
        Log.logData(AnalysisForParsingClass2.analysis_data, "- Data structure: " + data_structure);
        Log.logData(AnalysisForParsingClass2.analysis_data, Utils.generatePartingLine("~"));


        Pair<String, String> e_d = new Pair<String, String>(element, data_structure);
        if (mInnerElementsAndStructures == null) {
            mInnerElementsAndStructures = new ArrayList<>();
        }
        if(!mInnerElementsAndStructures.contains(e_d)) { // Avoid duplicated logs.
            mInnerElementsAndStructures.add(e_d);
            // analysis.Log data.
            Log.logData(AnalysisForParsingClass2.method_data, Utils.generatePartingLine("="));
            Log.logData(AnalysisForParsingClass2.method_data, "+ Element: " + element);
            Log.logData(AnalysisForParsingClass2.method_data, "+ Data structure: " + data_structure);
        }
    }

    public void setInnerElementsAndStructures(List<Pair<String, String>> e_ds){
        mInnerElementsAndStructures = e_ds;
    }

    public void storeTaintedChild(BU child){
        if(child == null) return;

        if(mTaintedChildren==null){
            mTaintedChildren=new HashSet<>();
            mTaintedChildren.add(child);
        } else {
            mTaintedChildren.add(child);
        }
    }

    public void setTaintedChildren(Set<BU> children){
        mTaintedChildren = children;
    }

    public void storeParameter(Value param, Integer index){
        if(index < 0 || param == null) return;

        if(mParameters == null){
            mParameters = new HashMap<>();
        }
        mParameters.put(param, index);
    }

    public void setParameters(Map<Value, Integer> params){
        mParameters = params;
    }

    public void storeDataStructure(String structure){
        Log.logData(AnalysisForUsingMethods.analysis_data, Utils.generatePartingLine("~"));
        Log.logData(AnalysisForUsingMethods.analysis_data, "- Data structure: " + structure);
        Log.logData(AnalysisForUsingMethods.analysis_data, Utils.generatePartingLine("~"));

        if(mDataStructures == null){
            mDataStructures = new ArrayList<>();
        }
        if(!mDataStructures.contains(structure)){
            mDataStructures.add(structure);
            // analysis.Log.
            Log.logData(AnalysisForUsingMethods.method_data, Utils.generatePartingLine("="));
            Log.logData(AnalysisForUsingMethods.method_data, "+ Data structure: " + structure);
        }
    }

    public void setDataStructures(List<String> structures){
        mDataStructures = structures;
    }

    public void storeEntryAssigns(AssignStmt as){
        if(mEntryAssigns == null){
            mEntryAssigns = new HashSet<>();
        }
        mEntryAssigns.add(as);
    }

    public void setEntryAssigns(Set<AssignStmt> entry_assigns){
        mEntryAssigns = entry_assigns;
    }

    public void setTaintedAttributes(Set<Integer> attributes){
        mTaintedAttributes= attributes;
    }
}
