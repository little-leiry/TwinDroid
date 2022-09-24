import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.toolkits.scalar.Pair;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Tainted {
    private SootMethod mMethod;
    private Value mValue;
    private String mElement;
    private List<SootMethod> mParents;

    private Unit mCallUnit;
    private Unit mStartUnit;
    private Set<Tainted> mTaintedChildren;


    private Set<Pair<String, Value>> mElementAndStructure;

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

    public Set<Tainted> getChildren(){
        return mTaintedChildren;
    }

    public Set<Pair<String, Value>> getElementAndStructure(){
        return mElementAndStructure;
    }


    public void storeElementAndCorrespondingStructure(String element, Value data_structure) {
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
            mElementAndStructure = new HashSet<>();
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

    public void setElementAndStructure(Set<Pair<String, Value>> e_ds){
        if(e_ds == null) return;

        if(mElementAndStructure == null){
            mElementAndStructure = new HashSet<>();
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
}
