import soot.ValueBox;

import java.util.Comparator;

public class VBComparator implements Comparator<ValueBox> {
    public int compare(ValueBox vb1, ValueBox vb2){
        String s1 = vb1.getValue().toString();
        String s2 = vb2.getValue().toString();
        if(s1.length() > s2.length()){
            return -1;
        } else if(s1.length() == s2.length()) {
            return 0;
        } else {
            return 1;
        }
    }
}
