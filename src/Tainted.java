import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class Tainted {
    private SootMethod mMethod;
    private List<Value> mTaintedValues;
    private String mOuterElement;
    private List<Tainted> mParents;
    private Unit mCallUnit;
    private Unit mStartUnit;
    private Set<Tainted> mTaintedChildren;
    private Map<Value, Integer> mParameters;
    private List<Pair<String, String>> mInnerElementsAndStructures;
    private List<String> mDataStructures;

    public Tainted(SootMethod method, List<Value> values, String element, List<Tainted> parents, Unit call_unit) {
        mMethod = method;
        mTaintedValues = values;
        mOuterElement = element;
        mParents = parents;
        mCallUnit = call_unit;
    }

    public Tainted(SootMethod method, List<Value> values, String element, Unit call_unit){
        mMethod = method;
        mTaintedValues = values;
        mOuterElement = element;
        mCallUnit = call_unit;
    }

    public Tainted(SootMethod method, List<Value> values, Unit call_unit){
        mMethod = method;
        mTaintedValues = values;
        mCallUnit = call_unit;
    }

    public Tainted(SootMethod method, List<Value> values){
        mMethod = method;
        mTaintedValues = values;
    }

    public Tainted(SootMethod method){
        mMethod = method;
    }

    public Tainted(){}

    public SootMethod getMethod(){
        return mMethod;
    }

    public List<Value> getTaintedValues(){
        return mTaintedValues;
    }

    public String getOuterElement(){
        return mOuterElement;
    }

    public List<Tainted> getParents(){
        return mParents;
    }

    public Unit getCallUnit(){
        return mCallUnit;
    }

    public Unit getStartUnit(){
        return mStartUnit;
    }

    public Set<Tainted> getTaintedChildren(){
        return mTaintedChildren;
    }

    public List<Pair<String, String>> getInnerElementAndStructure(){
        return mInnerElementsAndStructures;
    }

    public Map<Value, Integer> getParameters(){
        return mParameters;
    }

    public List<String> getDataStructures(){
        return mDataStructures;
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
        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));
        Log.logData(Log.analysis_data, "- Element: " + element);
        Log.logData(Log.analysis_data, "- Data structure: " + data_structure);
        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));


        Pair<String, String> e_d = new Pair<String, String>(element, data_structure);
        if (mInnerElementsAndStructures == null) {
            mInnerElementsAndStructures = new ArrayList<>();
        }
        if(!mInnerElementsAndStructures.contains(e_d)) { // Avoid duplicated logs.
            mInnerElementsAndStructures.add(e_d);
            // Log data.
            Log.logData(Log.method_data, Utils.generatePartingLine("="));
            Log.logData(Log.method_data, "+ Element: " + element);
            Log.logData(Log.method_data, "+ Data structure: " + data_structure);
        }
    }

    public void setInnerElementsAndStructures(List<Pair<String, String>> e_ds){
        mInnerElementsAndStructures = e_ds;
    }

    public void storeTaintedChildren(Tainted child){
        if(child == null) return;

        if(mTaintedChildren==null){
            mTaintedChildren=new HashSet<>();
            mTaintedChildren.add(child);
        } else {
            mTaintedChildren.add(child);
        }
    }

    public void setTaintedChildren(Set<Tainted> children){
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
        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));
        Log.logData(Log.analysis_data, "- Data structure: " + structure);
        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));

        if(mDataStructures == null){
            mDataStructures = new ArrayList<>();
        }
        if(!mDataStructures.contains(structure)){
            mDataStructures.add(structure);
            // Log.
            Log.logData(Log.method_data, Utils.generatePartingLine("="));
            Log.logData(Log.method_data, "+ Data structure: " + structure);
        }
    }

    public void setDataStructures(List<String> structures){
        mDataStructures = structures;
    }
}
