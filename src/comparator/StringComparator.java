package comparator;

import java.util.Comparator;
import java.util.List;

public class StringComparator implements Comparator<String> {
    public int compare(String s1, String s2){
        if(s1.length() > s2.length()){
            return -1;
        } else if(s1.length() == s2.length()){
            return 0;
        } else {
            return 1;
        }
    }
}
