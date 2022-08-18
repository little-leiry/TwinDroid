import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;

public class Tainted {

    public Tainted(){}

    // ParseResult<ParsedPermission> result = ParsedPermissionUtils.parsePermission(
    //          pkg, res, parser, sUseRoundIcon, input);
    public static Boolean isTaintedByEntryPoint(Unit unit, Value entry){
        if(unit instanceof AssignStmt) {
            AssignStmt as = (AssignStmt) unit;
            if (as.containsInvokeExpr()) {
                Value left = as.getLeftOp();
                InvokeExpr i = as.getInvokeExpr();
                if (Utility.isParameter(i, entry)) {
                    if (left.getType().toString().equals("android.content.pm.parsing.result.ParseResult")){
                        return true;
                    }
                }
            }
        }
        return false;
    }

    public static Boolean containTaintedValue(Unit unit, Value tainted_value){
        //parameter of the Invoke statement
        if(unit instanceof InvokeStmt){
            InvokeExpr i = (InvokeExpr) unit;
            return Utility.isParameter(i, tainted_value);
        }
        //used value of the assignment statement
        if(unit instanceof AssignStmt){
            AssignStmt as = (AssignStmt) unit;
            return Utility.containValue(as, tainted_value);
        }
        return false;
    }
}
