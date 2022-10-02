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

    private List<Pair<String, String>> mInnerElementAndStructure;

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

    public Tainted(SootMethod method, List<Value> values, Unit call_unit, Unit start_unit){
        mMethod = method;
        mTaintedValues = values;
        mCallUnit = call_unit;
        mStartUnit = start_unit;
    }

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

    public Set<Tainted> getChildren(){
        return mTaintedChildren;
    }

    public List<Pair<String, String>> getInnerElementAndStructure(){
        return mInnerElementAndStructure;
    }

    public Map<Value, Integer> getParameters(){
        return mParameters;
    }

    public void storeInnerElementAndStructure(String element, String data_structure) {

        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));
        Log.logData(Log.analysis_data, "- Element: " + element);
        Log.logData(Log.analysis_data, "- Data structure: " + data_structure);
        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));


        Pair<String, String> e_d = new Pair<String, String>(element, data_structure);
        if (mInnerElementAndStructure == null) { // This key does not exist.
            mInnerElementAndStructure = new ArrayList<>();
            mInnerElementAndStructure.add(e_d);
            // Log.
            Log.logData(Log.method_data, Utils.generatePartingLine("="));
            Log.logData(Log.method_data, "+ Element: " + element);
            Log.logData(Log.method_data, "+ Data structure: " + data_structure);
        } else {
            if(!mInnerElementAndStructure.contains(e_d)) { // Avoid duplicated logs.
                mInnerElementAndStructure.add(e_d);
                // Log data.
                Log.logData(Log.method_data, Utils.generatePartingLine("="));
                Log.logData(Log.method_data, "+ Element: " + element);
                Log.logData(Log.method_data, "+ Data structure: " + data_structure);
            }
        }
    }

    public void setInnerElementAndStructure(List<Pair<String, String>> e_ds){
        if(e_ds == null) return;

        if(mInnerElementAndStructure == null){
            mInnerElementAndStructure = new ArrayList<>();
        }
        mInnerElementAndStructure.addAll(e_ds);
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
        if(children == null) return;

        if(mTaintedChildren == null){
            mTaintedChildren = new HashSet<>();
        }
        mTaintedChildren.addAll(children);
    }

    public void storeParameter(Value param, Integer index){
        if(index < 0 || param == null) return;

        if(mParameters == null){
            mParameters = new HashMap<>();
        }
        mParameters.put(param, index);
    }
}
