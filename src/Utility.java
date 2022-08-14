import org.jetbrains.annotations.Nullable;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

import java.util.ArrayList;
import java.util.List;

public class Utility {

    public Utility(){}

    public static List<SootMethod> getMethodsOfClass(String className){
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        if (cls == null){ // the given class is not exist
            return null;
        }
        return cls.getMethods();
    }

    public static List<Body> getBodyOfMethod(String className, String methodName) {
        List<Body> bodies = new ArrayList<>();
        SootClass cls = Scene.v().getSootClassUnsafe(className);
        for (SootMethod sm : cls.getMethods()) {
            if (sm.getName().equals(methodName)) {
                bodies.add(sm.retrieveActiveBody());
            }
        }
        return bodies;
    }
}
