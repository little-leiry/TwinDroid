import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class Tainted {
    private SootMethod mMethod;
    private Value mValue;
    private String mElement;
    private List<Tainted> mParents;

    private Unit mCallUnit;

    private Unit mStartUnit;
    private Set<Tainted> mTaintedChildren;

    private Map<Value, Integer> mParameters;

    private List<Pair<String, Value>> mElementAndStructure;

    public Tainted(SootMethod method, Value value, String element, List<Tainted> parents, Unit call_unit) {
        mMethod = method;
        mValue = value;
        mElement = element;
        mParents = parents;
        mCallUnit = call_unit;
    }

    public Tainted(SootMethod method, Value value, String element, Unit call_unit){
        mMethod = method;
        mValue = value;
        mElement = element;
        mCallUnit = call_unit;
    }

    public Tainted(SootMethod method, Value value, Unit call_unit, Unit start_unit){
        mMethod = method;
        mValue = value;
        mCallUnit = call_unit;
        mStartUnit = start_unit;
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

    public List<Pair<String, Value>> getElementAndStructure(){
        return mElementAndStructure;
    }

    public Map<Value, Integer> getParameters(){
        return mParameters;
    }

    public void storeElementAndStructure(String element, Value data_structure) {
        String e;
        if(element == null){
            e = "NULL";
        } else {
            e = element;
        }
        String structure;
        if (data_structure == null){
            structure = "NULL";
        } else if (data_structure.toString().contains(".<")) {
            structure = data_structure.toString();
        } else {
            structure = data_structure.getType().toString();
        }

        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));
        Log.logData(Log.analysis_data, "- Element: " + e);
        Log.logData(Log.analysis_data, "- Data structure: " + structure);
        Log.logData(Log.analysis_data, Utils.generatePartingLine("~"));


        Pair<String, Value> e_d = new Pair<String, Value>(element, data_structure);
        if (mElementAndStructure == null) { // This key does not exist.
            mElementAndStructure = new ArrayList<>();
            mElementAndStructure.add(e_d);
            // Log.
            Log.logData(Log.method_data, Utils.generatePartingLine("="));
            Log.logData(Log.method_data, "+ Element: " + e);
            Log.logData(Log.method_data, "+ Data structure: " + structure);
        } else {
            if(!mElementAndStructure.contains(e_d)) { // Avoid duplicated logs.
                mElementAndStructure.add(e_d);
                // Log data.
                Log.logData(Log.method_data, Utils.generatePartingLine("="));
                Log.logData(Log.method_data, "+ Element: " + e);
                Log.logData(Log.method_data, "+ Data structure: " + structure);
                //Log.logData(method_data, Utils.generatePartingLine("-"));
            }
        }
    }

    public void setElementAndStructure(List<Pair<String, Value>> e_ds){
        if(e_ds == null) return;

        if(mElementAndStructure == null){
            mElementAndStructure = new ArrayList<>();
        }
        mElementAndStructure.addAll(e_ds);
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
