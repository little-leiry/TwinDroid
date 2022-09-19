import soot.Unit;
import soot.Value;

import java.util.HashMap;
import java.util.Map;

public class ElementInfo {
    private int mCaseNum = 0;
    private Value mCaseValue = null;
    private Map<Value, String> mValueToLikelyElement = new HashMap<Value, String>();
    private Map<String, String> mCaseIdToElement = new HashMap<String, String>();
    // element name => the unit associated with the element.
    private Map<String, Unit> mElementToUnit = new HashMap<String, Unit>();

    private Map<Value, String> mNumericValueToConcreteAssignment = new HashMap<Value, String>();

    public ElementInfo(){}

    public int getCaseNum(){
        return mCaseNum;
    }

    public void setCaseNum(int case_num){
        mCaseNum = case_num;
    }

    public Value getCaseValue(){
        return mCaseValue;
    }

    public void setCaseValue(Value case_value){
        mCaseValue = case_value;
    }

    public Map<String, String> getCaseIdToElement (){
        return mCaseIdToElement;
    }

    public void addCaseIdToElement(String id, String e){
        mCaseIdToElement.put(id, e);
    }

    public Map<Value, String> getValueToLikelyElement (){
        return mValueToLikelyElement;
    }

    public void addValueToLikelyElement(Value v, String e){
        mValueToLikelyElement.put(v, e);
    }

    public Map<Value, String> getNumericValueToConcreteAssignment (){
        return mNumericValueToConcreteAssignment;
    }

    public void addNumericValueToConcreteAssignment(Value v, String e){
        mNumericValueToConcreteAssignment.put(v, e);
    }

    public Map<String, Unit> getElementToUnit (){
        return mElementToUnit;
    }

    public void addElementToUnit(String e, Unit u){
        mElementToUnit.put(e, u);
    }

}
